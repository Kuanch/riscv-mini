// See LICENSE for license details.

package mini

import chisel3._
import chisel3.util._
import chisel3.experimental.BundleLiterals._

object Const {
  val PC_START = 0x200
  val PC_EVEC = 0x100
}

class DatapathIO(xlen: Int) extends Bundle {
  val host = new HostIO(xlen)
  val icache = Flipped(new CacheIO(xlen, xlen))
  val dcache = Flipped(new CacheIO(xlen, xlen))
  val ctrl = Flipped(new ControlSignals)
}

class FetchExecutePipelineRegister(xlen: Int) extends Bundle {
  val inst = chiselTypeOf(Instructions.NOP)
  val pc = UInt(xlen.W)
}

// class ExecuteWritebackPipelineRegister(xlen: Int) extends Bundle {
//   val inst = chiselTypeOf(Instructions.NOP)
//   val pc = UInt(xlen.W)
//   val alu = UInt(xlen.W)
//   val csr_in = UInt(xlen.W)
// }

class ExecuteMemoryPipelineRegister(xlen: Int) extends Bundle {
  val inst = UInt(32.W) // Current instruction
  val pc = UInt(xlen.W) // Program counter at execute stage
  val alu = UInt(xlen.W) // Result from the ALU to be used in MEM or WB
  val csr_in = UInt(xlen.W) // CSR input data
}

class MemoryWritebackPipelineRegister(xlen: Int) extends Bundle {
  val inst = UInt(32.W) // The current instruction
  val pc = UInt(xlen.W) // Program counter
  val alu = UInt(xlen.W) // Result from the ALU
  val csr_out = UInt(xlen.W) // CSR output data
  val wdata = SInt(xlen.W) // Data to be written to the register file
}

class Datapath(val conf: CoreConfig) extends Module {
  val io = IO(new DatapathIO(conf.xlen))
  val csr = Module(new CSR(conf.xlen))
  val regFile = Module(new RegFile(conf.xlen))
  val alu = Module(conf.makeAlu(conf.xlen))
  val immGen = Module(conf.makeImmGen(conf.xlen))
  val brCond = Module(conf.makeBrCond(conf.xlen))

  import Control._

  /** Pipeline State Registers * */

  /** *** Fetch / Execute Registers ****
    */
  val fe_reg = RegInit(
    (new FetchExecutePipelineRegister(conf.xlen)).Lit(
      _.inst -> Instructions.NOP,
      _.pc -> 0.U
    )
  )

  /** *** Execute / Write Back Registers ****
  val ew_reg = RegInit(
    (new ExecuteWritebackPipelineRegister(conf.xlen)).Lit(
      _.inst -> Instructions.NOP,
      _.pc -> 0.U,
      _.alu -> 0.U,
      _.csr_in -> 0.U
    )
  )
  */

  /** *** Execute / Memory Registers ****
    */
  val em_reg = RegInit(
    (new ExecuteMemoryPipelineRegister(conf.xlen)).Lit(
      _.inst -> Instructions.NOP,
      _.pc -> 0.U,
      _.alu -> 0.U,
      _.csr_in -> 0.U
    )
  )

  /** *** Memory / Write Back Registers ****
    */
  val mw_reg = RegInit(
    (new MemoryWritebackPipelineRegister(conf.xlen)).Lit(
      _.inst -> Instructions.NOP,
      _.pc -> 0.U,
      _.alu -> 0.U,
      _.csr_out -> 0.U,
      _.wdata -> 0.S
    )
  )

  /** **** Control signals ****
    */
  val st_type = Reg(io.ctrl.st_type.cloneType)
  val ld_type = Reg(io.ctrl.ld_type.cloneType)
  val m_wb_sel = Reg(io.ctrl.wb_sel.cloneType)
  val m_wb_en = Reg(Bool())
  val w_wb_sel = Reg(io.ctrl.wb_sel.cloneType)
  val w_wb_en = Reg(Bool())
  val csr_cmd = Reg(io.ctrl.csr_cmd.cloneType)
  val illegal = Reg(Bool())
  val pc_check = Reg(Bool())

  /** **** Fetch ****
    */
  val started = RegNext(reset.asBool)
  val stall = !io.icache.resp.valid || !io.dcache.resp.valid
  val pc = RegInit(Const.PC_START.U(conf.xlen.W) - 4.U(conf.xlen.W))
  // Next Program Counter
  val next_pc = MuxCase(
    pc + 4.U,
    IndexedSeq(
      stall -> pc,
      csr.io.expt -> csr.io.evec,
      (io.ctrl.pc_sel === PC_EPC) -> csr.io.epc,
      ((io.ctrl.pc_sel === PC_ALU) || (brCond.io.taken)) -> (alu.io.sum >> 1.U << 1.U),
      (io.ctrl.pc_sel === PC_0) -> pc
    )
  )
  val inst =
    Mux(started || io.ctrl.inst_kill || brCond.io.taken || csr.io.expt, Instructions.NOP, io.icache.resp.bits.data)
  pc := next_pc
  io.icache.req.bits.addr := next_pc
  io.icache.req.bits.data := 0.U
  io.icache.req.bits.mask := 0.U
  io.icache.req.valid := !stall
  io.icache.abort := false.B

  // Pipelining
  when(!stall) {
    fe_reg.pc := pc
    fe_reg.inst := inst
  }

  /** **** Execute ****
    */
  io.ctrl.inst := fe_reg.inst

  // regFile read
  val rd_addr = fe_reg.inst(11, 7)
  val rs1_addr = fe_reg.inst(19, 15)
  val rs2_addr = fe_reg.inst(24, 20)
  regFile.io.raddr1 := rs1_addr
  regFile.io.raddr2 := rs2_addr

  // gen immdeates
  immGen.io.inst := fe_reg.inst
  immGen.io.sel := io.ctrl.imm_sel

  // bypass
  // val wb_rd_addr = ew_reg.inst(11, 7)
  val wb_rd_addr = em_reg.inst(11, 7)
  val rs1hazard = m_wb_en && rs1_addr.orR && (rs1_addr === wb_rd_addr)
  val rs2hazard = m_wb_en && rs2_addr.orR && (rs2_addr === wb_rd_addr)
  // val rs1 = Mux(wb_sel === WB_ALU && rs1hazard, ew_reg.alu, regFile.io.rdata1)
  // val rs2 = Mux(wb_sel === WB_ALU && rs2hazard, ew_reg.alu, regFile.io.rdata2)
  val rs1 = Mux(m_wb_sel === WB_ALU && rs1hazard, em_reg.alu, regFile.io.rdata1)
  // val rs2 = Mux(m_wb_sel === WB_ALU && rs2hazard, em_reg.alu, regFile.io.rdata2)
  // bypass wb to mem
  val bypass_wb_to_mem = (mw_reg.inst(11, 7) === em_reg.inst(24, 20)) && ((w_wb_en && io.ctrl.st_type === ST_SW) || (w_wb_en && io.ctrl.ld_type === LD_LW))
  val rs2 = Mux(bypass_wb_to_mem, mw_reg.wdata.asUInt, Mux(m_wb_sel === WB_ALU && rs2hazard, em_reg.alu, regFile.io.rdata2))

  // ALU operations
  alu.io.A := Mux(io.ctrl.A_sel === A_RS1, rs1, fe_reg.pc)
  alu.io.B := Mux(io.ctrl.B_sel === B_RS2, rs2, immGen.io.out)
  alu.io.alu_op := io.ctrl.alu_op

  // Branch condition calc
  brCond.io.rs1 := rs1
  brCond.io.rs2 := rs2
  brCond.io.br_type := io.ctrl.br_type

  // D$ access
  // val daddr = Mux(stall, ew_reg.alu, alu.io.sum) >> 2.U << 2.U
  // val woffset = (alu.io.sum(1) << 4.U).asUInt | (alu.io.sum(0) << 3.U).asUInt
  // io.dcache.req.valid := !stall && (io.ctrl.st_type.orR || io.ctrl.ld_type.orR)
  // io.dcache.req.bits.addr := daddr
  // io.dcache.req.bits.data := rs2 << woffset
  // io.dcache.req.bits.mask := MuxLookup(Mux(stall, st_type, io.ctrl.st_type), "b0000".U)(
  //   Seq(ST_SW -> "b1111".U, ST_SH -> ("b11".U << alu.io.sum(1, 0)), ST_SB -> ("b1".U << alu.io.sum(1, 0)))
  // )
  // D$ access
  val daddr = Mux(stall, em_reg.alu, alu.io.sum) >> 2.U << 2.U
  val woffset = (alu.io.sum(1) << 4.U).asUInt | (alu.io.sum(0) << 3.U).asUInt
  io.dcache.req.valid := !stall && (io.ctrl.st_type.orR || io.ctrl.ld_type.orR)
  io.dcache.req.bits.addr := daddr
  io.dcache.req.bits.data := rs2 << woffset
  io.dcache.req.bits.mask := MuxLookup(Mux(stall, st_type, io.ctrl.st_type), "b0000".U)(
    Seq(ST_SW -> "b1111".U, ST_SH -> ("b11".U << alu.io.sum(1, 0)), ST_SB -> ("b1".U << alu.io.sum(1, 0)))
  )

  // Pipelining
  when(reset.asBool || !stall && csr.io.expt) {
    st_type := 0.U
    ld_type := 0.U
    m_wb_en := false.B
    w_wb_en := false.B
    csr_cmd := 0.U
    illegal := false.B
    pc_check := false.B
  }.elsewhen(!stall && !csr.io.expt) {
    // ew_reg.pc := fe_reg.pc
    // ew_reg.inst := fe_reg.inst
    // ew_reg.alu := alu.io.out
    // ew_reg.csr_in := Mux(io.ctrl.imm_sel === IMM_Z, immGen.io.out, rs1)
    em_reg.pc := fe_reg.pc
    em_reg.inst := fe_reg.inst
    em_reg.alu := alu.io.out
    em_reg.csr_in := Mux(io.ctrl.imm_sel === IMM_Z, immGen.io.out, rs1)
    mw_reg.inst := em_reg.inst
    mw_reg.pc := em_reg.pc
    mw_reg.alu := em_reg.alu
    mw_reg.csr_out := csr.io.out
    st_type := io.ctrl.st_type
    ld_type := io.ctrl.ld_type
    m_wb_sel := io.ctrl.wb_sel
    m_wb_en := io.ctrl.wb_en
    w_wb_sel := m_wb_sel
    w_wb_en := m_wb_en
    csr_cmd := io.ctrl.csr_cmd
    illegal := io.ctrl.illegal
    pc_check := io.ctrl.pc_sel === PC_ALU
  }

  // Load
  // val loffset = (ew_reg.alu(1) << 4.U).asUInt | (ew_reg.alu(0) << 3.U).asUInt
  val loffset = (em_reg.alu(1) << 4.U).asUInt | (em_reg.alu(0) << 3.U).asUInt
  val lshift = io.dcache.resp.bits.data >> loffset
  // load := MuxLookup(ld_type, io.dcache.resp.bits.data.zext)(
  mw_reg.wdata := MuxLookup(ld_type, io.dcache.resp.bits.data.zext)(
    Seq(
      LD_LH -> lshift(15, 0).asSInt,
      LD_LB -> lshift(7, 0).asSInt,
      LD_LHU -> lshift(15, 0).zext,
      LD_LBU -> lshift(7, 0).zext
    )
  )

  // CSR access
  csr.io.stall := stall
  // csr.io.in := ew_reg.csr_in
  csr.io.in := em_reg.csr_in
  csr.io.cmd := csr_cmd
  // csr.io.inst := ew_reg.inst
  // csr.io.pc := ew_reg.pc
  // csr.io.addr := ew_reg.alu
  csr.io.inst := em_reg.inst
  csr.io.pc := em_reg.pc
  csr.io.addr := em_reg.alu
  csr.io.illegal := illegal
  csr.io.pc_check := pc_check
  csr.io.ld_type := ld_type
  csr.io.st_type := st_type
  io.host <> csr.io.host

  // Regfile Write
  // val regWrite =
  //   MuxLookup(wb_sel, ew_reg.alu.zext)(
  //     Seq(WB_MEM -> load, WB_PC4 -> (ew_reg.pc + 4.U).zext, WB_CSR -> csr.io.out.zext)
  //   ).asUInt
  val regWrite = 
       MuxLookup(w_wb_sel, mw_reg.alu.zext)(
         Seq(WB_MEM -> mw_reg.wdata, WB_PC4 -> (mw_reg.pc + 4.U).zext, WB_CSR -> mw_reg.csr_out.zext)
       ).asUInt

  // regFile.io.wen := w_wb_en && !stall && !wb_excp
  regFile.io.wen := w_wb_en && !stall
  regFile.io.waddr := mw_reg.inst(11, 7)
  regFile.io.wdata := regWrite

  // Abort store when there's an excpetion
  io.dcache.abort := csr.io.expt

  // TODO: re-enable through AOP
  printf(
    "PC: %x, %x, %x, INST: %x, %x, %x, stall:%x, wen:%x, waddr: %x, wdata: %x, wen:%x, wb addr: %x, wb data: %x, wwbsel: %x, mwalu: %x\n",
    fe_reg.pc,
    em_reg.pc,
    mw_reg.pc,
    fe_reg.inst,
    em_reg.inst,
    mw_reg.inst,
    stall,
    io.dcache.req.valid,
    io.dcache.req.bits.addr,
    io.dcache.req.bits.data,
    regFile.io.wen,
    regFile.io.waddr,
    regFile.io.wdata,
    w_wb_sel, mw_reg.alu
  )
}