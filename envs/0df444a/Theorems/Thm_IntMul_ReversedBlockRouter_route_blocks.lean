-- Prove2me | Theorems.Thm_IntMul_ReversedBlockRouter_route_blocks
-- name    : IntMul.ReversedBlockRouter.route_blocks
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T09:34:19.156067+00:00
-- url     : https://prove2.me/theorems/784d88ed-7a84-46dd-887a-a7196520780a
-- title:
--   Actual six-tape low-significance-first block routing with complete execution cost
-- statement:
--   Let x and y be arbitrary binary words, with n=|x|, w=|y| and B=val(y)+1. The fixed six-tape routing machine reverses x, physically copies the reversed word and descriptor into a scratch request, and writes B-bit separated blocks of the reversed word on its output. Blocks are ordered from least significant to most significant; bits within each block are little-endian. There is no trailing separator. For some actual execution length t,
--
--   $$t\le 13n+\left\lfloor\frac{n-1}{B}\right\rfloor(4w+4)+10w+23,$$
--
--   and the entire terminal configuration equals the specified final frame. Natural subtraction interprets n-1 as zero for empty input. The original input is preserved, the reverse scratch and routed request are exact, both delimited descriptor tapes are restored, and all six final head positions are specified. Every copy, delimiter write, rewind and all three caller returns are included. Empty words and arbitrarily padded descriptors are allowed. This gives a physical low-significance-first digit-routing interface for integer multiplication, with no uncharged tape reset.
-- source:
--   Original complete physical digit-routing execution. Owns all layout, relay and full configuration proofs privately, using accepted word reversal, block splitting and finite-caller simulation. Written by Codex.

import Definitions.Def_IntMul_ReversedBlockRouter
import Mathlib.Tactic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeDrop
import Theorems.Thm_IntMul_TapeReverse_reverse_first_operand
import Theorems.Thm_IntMul_CountedBlockSplitter_split_blocks
import Theorems.Thm_IntMul_FiniteCaller_simulate_run

open IntMul IntMul.ReversedBlockRouter

theorem IntMul.ReversedBlockRouter.route_blocks (x y : List Bool) :
    ∃ t : ℕ,
      t ≤ 13*x.length+((x.length-1)/CountedBlockSplitter.blockSize y)*(4*y.length+4)+
        10*y.length+23 ∧
      machine.step^[t] (machine.initCfg x y)=finalFrame x y ∧
      (machine.step^[t] (machine.initCfg x y)).state=machine.qHalt := by sorry
