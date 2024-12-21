/*
 * Copyright (c) 2024 Your Name
 * SPDX-License-Identifier: Apache-2.0
 */

`default_nettype none


// Integrated module for Tiny Tapeout and Octa16 processor
module tt_um_example (
    input  wire [7:0] ui_in,    // Dedicated inputs
    output wire [7:0] uo_out,   // Dedicated outputs
    input  wire [7:0] uio_in,   // IOs: Input path
    output wire [7:0] uio_out,  // IOs: Output path
    output wire [7:0] uio_oe,   // IOs: Enable path (active high: 0=input, 1=output)
    input  wire       ena,      // always 1 when the design is powered, so you can ignore it
    input  wire       clk,      // clock
    input  wire       rst_n     // reset_n - low to reset
);

    // Signal declarations
    wire reset = ~rst_n;  // Active-low reset converted to active-high

    // Signals connecting the Octa16 processor
    wire [15:0] Ext_WriteData;  // Data to write to instruction memory
    wire [3:0]  Ext_DataAdr;    // Address for instruction memory write
    wire Ext_MemWrite;          // External memory write enable
    wire [3:0] DataAddr;        // Data memory address
    wire [7:0] dIn;             // Data input for register file

    // Map Tiny Tapeout inputs and outputs to Octa16
    assign Ext_WriteData = {ui_in, uio_in[7:0]}; // Combine ui_in and uio_in for write data
    assign Ext_DataAdr   = ui_in[3:0];           // Lower 4 bits of ui_in as address
    assign Ext_MemWrite  = ui_in[4];            // Bit 4 of ui_in as memory write enable

    // Outputs from Octa16 processor
    assign uo_out = dIn;                        // Processor data output to dedicated outputs
    assign uio_out = 8'b0;                      // Unused outputs set to 0
    assign uio_oe = 8'b0;                       // No bidirectional pins used

    // Octa16 processor instance
    Octa16 processor (
        .clk(clk),
        .reset(reset),
        .Ext_MemWrite(Ext_MemWrite),
        .Ext_WriteData(Ext_WriteData),
        .Ext_DataAdr(Ext_DataAdr),
        .DataAddr(DataAddr),
        .dIn(dIn)
    );

    // List all unused inputs to prevent warnings
    wire _unused = &{ena, 1'b0};

endmodule


/*
* -------
*

module tt_um_example (
    input  wire [7:0] ui_in,    // Dedicated inputs
    output wire [7:0] uo_out,   // Dedicated outputs
    input  wire [7:0] uio_in,   // IOs: Input path
    output wire [7:0] uio_out,  // IOs: Output path
    output wire [7:0] uio_oe,   // IOs: Enable path (active high: 0=input, 1=output)
    input  wire       ena,      // always 1 when the design is powered, so you can ignore it
    input  wire       clk,      // clock
    input  wire       rst_n     // reset_n - low to reset
);

  // All output pins must be assigned. If not used, assign to 0.
  assign uo_out  = ui_in + uio_in;  // Example: ou_out is the sum of ui_in and uio_in
  assign uio_out = 0;
  assign uio_oe  = 0;

  // List all unused inputs to prevent warnings
  wire _unused = &{ena, clk, rst_n, 1'b0};

endmodule
*/
module Octa16(
    input clk, reset,
    input Ext_MemWrite,                   // External Memory Write Enable
    input [15:0] Ext_WriteData,           // Data to be written to instruction memory
    input [3:0] Ext_DataAdr,             // Address to write to instruction memory
    input [3:0] DataAddr,                // Address selection for data operations
    output [7:0] dIn                     // Data In (for register file)
);

    wire [3:0] pcP, pcN;
    wire [15:0] Inst;
    wire [7:0] aluOut, pcSel, imm;
    wire bSel, reg_wr, mem_wr;
    wire [2:0] rs1, rs2, rd, func, opcode;
    wire [7:0] r1, r2;
    wire alu_s1, alu_s2, flag;
    wire [2:0] alu_op;
    wire [7:0] dataOut;
    wire [1:0] wb_ctrl;
    wire branch, branchOut, doBranch, doJump;
    wire [2:0] branch_ctrl;
    wire [20:0] u;
    wire [7:0] out1, out2;

    // PC and Instruction Fetch
    adder_8 pcAdd (.A({4'b0, pcP}), .B(8'b1), .Cin(1'b0), .Sum({u[3:0], pcN}));
    mux21 PC_MUX (.d0({4'b0, pcN}), .d1(aluOut), .sel(bSel), .y(pcSel));
    regs #(8) PC (.clk(clk), .rst(reset), .in(pcSel), .out({u[7:4], pcP}), .en(1'b1));
    
    // Instruction Memory with External Write Capability
    instmem #(12) Inst_Mem (
        .clk(clk), 
        .memW(Ext_MemWrite),              // Write Enable for Instruction Memory
        .addr(Ext_DataAdr),               // Address to write data to instruction memory
        .dataW(Ext_WriteData),            // Data to write into instruction memory
        .dataR(Inst)                      // Instruction Read
    );

    // Decoder and Register File
    decoder Decoder_Unit (.instIn(Inst), .rs1(rs1), .rs2(rs2), .rd(rd), .func(func), .opcode(opcode), .imm(imm));
    reg_ff #(8) Reg_File (.clk(clk), .wrEn(reg_wr), .rs1(rs1), .rs2(rs2), .rd(rd), .r1(r1), .r2(r2), .rst(reset), .dIn(dIn));
    
    // ALU and ALU Control
    mux21 ALU_MUX_1 (.d0(r1), .d1({4'b0, pcP}), .sel(alu_s1), .y(out1));
    mux21 ALU_MUX_2 (.d0(imm), .d1(r2), .sel(alu_s2), .y(out2));
    alu ALU (.a(out1), .b(out2), .ctrl(alu_op), .flag(flag), .out(aluOut));
    
    // Data Memory Access (Only for Data Memory)
    datamem #(4) Data_Mem (
        .clk(clk), 
        .memW(mem_wr),                  // Only handle writes for data memory
        .addr(DataAddr),                // Data memory address
        .dataW(r2),                     // Data to write into memory
        .dataR(dataOut)                 // Data read from memory
    );
    
    // Write Back MUX
    mux31 #(8) WB_MUX (.a(dataOut), .b(aluOut), .c({4'b0, pcN}), .s(wb_ctrl), .y(dIn));

    // Control and Branch Logic
    controller Control_Unit (.func(func), .op(opcode), .reg_wr(reg_wr), .mem_wr(mem_wr), .flag(flag), .doBranch(doBranch), .doJump(doJump), .wb_ctrl(wb_ctrl), .alu_op(alu_op), .branch_ctrl(branch_ctrl), .alu_s1(alu_s1), .alu_s2(alu_s2));
    branchCtrl Branch_Control (.bCtrl(branch_ctrl), .r1(r1), .r2(r2), .bSel(branchOut));
    and Branch (branch, branchOut, doBranch);
    or Jump (bSel, branch, doJump);

    // Data Address Selection Logic
    assign DataAddr = Ext_MemWrite ? Ext_DataAdr : pcP;

endmodule


module adder_8(
    input [7:0] A,
    input [7:0] B,
    input Cin,
    output [7:0] Sum
);

    wire C4;  // Carry between lower and upper 4-bit additions
    wire Cout;
    // Instantiate lower 4-bit CLA
    cla lower_4bit (
        .A(A[3:0]), 
        .B(B[3:0]), 
        .Cin(Cin), 
        .S(Sum[3:0]), 
        .Cout(C4)
    );

    // Instantiate upper 4-bit CLA with carry-in from the lower 4-bit adder
    cla upper_4bit (
        .A(A[7:4]), 
        .B(B[7:4]), 
        .Cin(C4), 
        .S(Sum[7:4]), 
        .Cout(Cout)
    );

endmodule


module alu(
    input wire [7:0] a, b,
    input wire [2:0] ctrl,
    input wire flag,
    output reg [7:0] out
);

    wire [7:0] add_out;
    reg [7:0] a_temp, b_temp;
    reg cin;
    wire [15:0] sext_rs1 = {{8{a[7]}}, a};
    wire [15:0] sra_rslt = sext_rs1 >> b[2:0];

    // Instantiate adder module
    adder_8 adder (
        .A(a_temp), 
        .B(b_temp), 
        .Cin(cin), 
        .Sum(add_out)
    );

    always @(*) begin
        // Default values to avoid latches
        out = 8'b0;
        a_temp = 8'b0;
        b_temp = 8'b0;
        cin = 1'b0; 

        case(ctrl)
            3'b000: begin
               a_temp = a;
                b_temp = flag ? ~b : b;
                cin = flag;
                out = add_out;
            end

            3'b001: begin
                if (flag == 1)
                    out = ~(a & b); // NAND
                else
                    out = ~(a | b); // NOR
            end

            3'b010: begin
                out = (a < b) ? 8'b1 : 8'b0; // SLTU
            end

            3'b011: begin
                if (flag == 1)
                    out = a << b[2:0]; // SLL
                else
                    out = a >> b[2:0]; // SRL
            end

            3'b100: begin
                out = sra_rslt;// SRA
            end

            default: begin
                out = 8'b0;
            end
        endcase
    end
endmodule


module branchCtrl(input wire [2:0] bCtrl,
                  input wire [7:0] r1, r2,
                  output reg bSel);
    
    wire [7:0] condinv = ~r2;
    wire [8:0] sum = {1'b1, condinv} + {1'b0, r1} + {8'b0, 1'b1};
    wire LT = (r1[7] ^ r2[7]) ? r1[7] : sum[8];
    wire LTU = sum[8];
    wire is_sum_zero = sum[7:0] == 8'b0;

  always@(*)
    begin
      bSel = 1'b0;
      case(bCtrl)
        3'b000: bSel = is_sum_zero; // BEQ
          
        3'b001: bSel = !is_sum_zero; // BNE
          
        3'b010: bSel = LT; // BLT
          
        3'b011: bSel = LTU; // BLTU
          
        3'b100: bSel = !LT; // BGE
         
        3'b101: bSel = !LTU; // BGEU
          
        default: bSel = 1'b0;
      endcase
    end
endmodule


module cla(
    input [3:0] A, 
    input [3:0] B, 
    input Cin, 
    output [3:0] S, 
    output Cout
);

    wire [3:0] P;       // Propagate signals
    wire [3:0] G;       // Generate signals
    wire [3:0] C;       // Carry signals

    assign P = A ^ B;   // Propagate: XOR for each bit
    assign G = A & B;   // Generate: AND for each bit

    // Carry chain calculation
    assign C[0] = Cin;
    assign C[1] = G[0] | (P[0] & C[0]);
    assign C[2] = G[1] | (P[1] & C[1]);
    assign C[3] = G[2] | (P[2] & C[2]);
    assign Cout = G[3] | (P[3] & C[3]);

    // Sum calculation
    assign S[0] = P[0] ^ C[0];
    assign S[1] = P[1] ^ C[1];
    assign S[2] = P[2] ^ C[2];
    assign S[3] = P[3] ^ C[3];

endmodule



module controller(input wire [2:0]func, 
            input wire [2:0]op,
            output reg reg_wr, mem_wr, flag, doBranch, doJump,
            output reg [1:0] wb_ctrl,
            output reg [2:0]alu_op, branch_ctrl,
            output reg alu_s1, alu_s2);
    
    always@(*)
        begin
            reg_wr = 1'b0;
            alu_s1 = 1'b0;
            alu_s2 = 1'b0;
            alu_op = 3'b0;
            mem_wr = 1'b0;
            doBranch = 1'b0;
            flag = 1'b0;
            wb_ctrl = 2'b11;
            //wb_ctrl = 2'b0;
            case(op)
                3'b000: // R-TYPE Instructions
                    begin
                        reg_wr = 1'b1;
                        wb_ctrl = 2'b00;
                        alu_s1 = 1'b0;
                        alu_s2 = 1'b1;
                        
                        case(func) 
                            3'b000: begin // ADD
                                alu_op = 3'b000;
                                flag = 1'b0;
                            end
                            3'b001: begin // SUB
                                alu_op = 3'b000;
                                flag = 1'b1;
                            end
                            3'b010: begin // NAND
                                alu_op = 3'b001;
                                flag = 1'b0;
                            end
                            3'b011: begin // NOR
                                alu_op = 3'b001;
                                flag = 1'b1;
                            end
                            3'b100: begin // SLTU
                                alu_op = 3'b010;
                            end
                            3'b101: begin // SLL
                                alu_op = 3'b011;
                                flag = 1'b0;
                            end
                            3'b110: begin // SRL
                                alu_op = 3'b011;
                                flag = 1'b1;
                            end
                            3'b111: begin // SRA
                                alu_op = 3'b100;
                            end
                        endcase
                    end
                3'b001: // I-TYPE Instrcutions
                    begin
                        reg_wr = 1'b1;
                        wb_ctrl = 2'b00;
                        case(func) 
                            3'b000: begin // ADDI
                                alu_op = 3'b000;
                                flag = 1'b0;
                            end
                            3'b010: begin // NANDI
                                alu_op = 3'b001;
                                flag = 1'b0;
                            end
                            3'b011: begin // NORI
                                alu_op = 3'b001;
                                flag = 1'b1;
                            end
                            3'b100: begin // SLTI
                                alu_op = 3'b010;
                            end
                            3'b101: begin // SLLI
                                alu_op = 3'b011;
                                flag = 1'b0;
                            end
                            3'b110: begin // SRLI
                                alu_op = 3'b011;
                                flag = 1'b1;
                            end
                            3'b111: begin // SRAI
                                alu_op = 3'b100;
                            end
                        endcase
                    end
                3'b010: // L-TYPE Instruction
                    begin
                        reg_wr = 1'b1;
                        alu_op = 3'b000;
                        wb_ctrl = 2'b01;
                        //need to be done
                    end
                3'b011: // S-TYPE Instruction
                    begin
                        mem_wr = 1'b1;
                        alu_op = 3'b000;
                        //need to be done
                    end
                3'b100: // B-TYPE Instructions
                    begin
                        branch_ctrl = func;
                        doBranch = 1'b1;
                        alu_s1 = 1'b1;
                        alu_op = 3'b000;
                    end
                3'b101: // J-TYPE Instructions
                    begin
                        case(func)
                            3'b000: // JAL
                                begin
                                    reg_wr = 1'b1;
                                    alu_s1 = 1'b1;
                                    wb_ctrl = 2'b10;
                                    alu_op = 3'b000;
                                    doJump = 1'b1;
                                end
                            3'b100: // JALR
                                begin
                                    reg_wr = 1'b1;
                                    wb_ctrl = 2'b10;
                                    alu_op = 3'b000;
                                    doJump = 1'b1;
                                end
                        endcase
                    end
                3'b110: // U-TYPE Instructions
                    begin
                        case(func)
                            3'b000: //AUIR
                                begin
                                    reg_wr = 1'b1;
                                    alu_s1 = 1'b1;
                                    wb_ctrl = 2'b00;
                                    alu_op = 3'b000;
                                end
                            3'b001: //ADDPC
                                begin
                                    reg_wr = 1'b1;
                                    wb_ctrl = 2'b00;
                                    alu_op = 3'b000;
                                end
                        endcase
                    end
            endcase
        end
endmodule


module datamem #(parameter SIZE = 4) (clk, memW, addr, dataW, dataR);
    input wire clk;
    input wire memW;
    input wire [SIZE-1:0] addr;
    input wire [7:0] dataW;
    output wire [7:0] dataR;
    reg [7:0] mem [(SIZE-1):0];

    always @(posedge clk) begin
        if (memW) begin
            mem[addr] <= dataW;
        end
    end
    assign dataR = mem[addr];
endmodule

module decoder(input wire [15:0]instIn,
         output reg [2:0]rs1, rs2, rd,
         output reg [2:0]func,
         output reg [2:0]opcode,
         output reg [7:0]imm);
 
  always@(*)
    begin
      opcode = instIn[2:0];
      rs1 = 3'b0;
      rs2 = 3'b0;
      rd = 3'b0;
      func = 3'b0;
     
      case(opcode)
        3'b000: //R-Type
          begin
            rs1 = instIn[11:9];
            rs2 = instIn[14:12];
            rd = instIn[8:6];
            func = instIn[5:3];
          end
        3'b001: //I-Type
          begin
            rs1 = instIn[11:9];
            rd = instIn[8:6];
            func = instIn[5:3];
            imm = {{5{instIn[15]}},instIn[14:12]};
          end
        3'b010: //L-Type
          begin
            rs1 = instIn[11:9];
            rd = instIn[8:6];
            imm = {{2{instIn[15]}},instIn[14:12], instIn[5:3]};
          end
        3'b011: //S-Type
          begin
            rs1 = instIn[11:9];
            rd = instIn[8:6];
            imm = {{2{instIn[15]}},instIn[14:12], instIn[5:3]};
          end
        3'b100: //B-Type
          begin
            rs2 = instIn[14:12];
            rs1 = instIn[11:9];
            func = instIn[5:3];
            imm = {{5{instIn[15]}}, instIn[8:6]};
          end
        3'b101:
          begin
            rd = instIn[8:6];
            func = instIn[5:3];
            case(func)
              3'b000: begin imm = {1'b0, instIn[15:9]}; end   // JAL
              3'b100: begin imm = {instIn[15:12], 4'b0}; rs1 = instIn[11:9]; end  // JALR
            endcase
          end
        3'b110:
          begin
            rd = instIn[8:6];
            func = instIn[5:3];
            case(func)
              3'b001: begin imm = {{2{instIn[15]}}, instIn[14:9]}; end   // ADDPC
              3'b000: begin imm = {instIn[15:12],4'b0}; rs1 = instIn[11:9]; end  // AUIR
            endcase
          end
endcase 
end 
endmodule


module instmem #(parameter SIZE = 16) (clk, memW, addr, dataW, dataR);
    input wire clk;
    input wire memW;
    input wire [3:0] addr;
    input wire [15:0] dataW;
    output wire [15:0] dataR;
    reg [15:0] mem [(SIZE-1):0];

    always @(posedge clk) begin
        if (memW) begin
            mem[addr] <= dataW;
        end
    end
    assign dataR = mem[addr];
endmodule

module mux21(d0, d1, sel, y);

    parameter WIDTH = 8;
    input [WIDTH-1:0] d0, d1;
    input sel;
    output [WIDTH-1:0] y;

    assign y = sel ? d1 : d0;

endmodule


module mux31 #(parameter N = 8) (a, b, c, s, y);
  input wire [N-1:0] a; //00
  input wire [N-1:0] b; //01
  input wire [N-1:0] c; //10
  input wire [1:0] s;
  output wire [N-1:0] y;
  
  wire [N-1:0] mux1;
  mux21 m1(a, b, s[0], mux1);
  mux21 m2(mux1, c, s[1], y);
endmodule


module reg_ff #(parameter DATA_WIDTH = 8) (clk, wrEn, rs1, rs2, rd, r1, r2, rst, dIn);
  input wire clk, wrEn, rst;
  input wire [2:0] rs1, rs2, rd;
  input wire [DATA_WIDTH-1:0] dIn;
  output wire [DATA_WIDTH-1:0] r1, r2;
  reg [DATA_WIDTH-1:0] reg_file [0:7];
  integer i = 0;
  initial begin
    for (i = 0; i < 8; i = i + 1) 
      begin
        reg_file[i] = 0;
      end
  end
  always @(posedge clk) begin
    if (rst) begin
      reg_file[0] <= 0;
      reg_file[1] <= 0;  // substitute with other values
      reg_file[2] <= 0;  // substitute with other values
      reg_file[3] <= 0;  // substitute with other values
      reg_file[4] <= 0;
      reg_file[5] <= 0;
      reg_file[6] <= 0;
      reg_file[7] <= 0;
    end else begin
      reg_file[rd] <= (wrEn ? dIn : ( (rd != 0) ? reg_file[rd] : 0));
    end
  end
/*
  always @(posedge clk) 
    reg_file[rd] <= (wrEn && rd != 0) ? dIn : reg_file[rd];
*/
  // register file read logic (combinational)
  assign r1 = (rs1 != 0 ) ? reg_file[rs1] : 0;
  assign r2 = (rs2 != 0 ) ? reg_file[rs2] : 0;
endmodule


module regs #(parameter N = 8) (clk, rst, in, out, en);
  input wire clk;
  input wire rst;
  input wire en;
  input wire [N-1:0] in;
  output reg [N-1:0] out;
  always @(posedge clk or posedge rst) 
    begin
      if (rst)
        out <= 0;
      else if (en) 
        out <= in;
    end
endmodule
