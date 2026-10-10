-- Prove2me | Theorems.Thm_IntMul_CountedBlockSplitter_split_blocks
-- name    : IntMul.CountedBlockSplitter.split_blocks
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T08:36:05.893354+00:00
-- url     : https://prove2.me/theorems/86475f87-3f67-418c-8030-ebc469f6a884
-- title:
--   Actual descriptor-sized digit block splitter with complete clock and restored frame
-- statement:
--   For every binary payload x and descriptor y, one fixed four-tape, five-symbol, 29-state multitape Turing machine splits x into B-bit blocks, B=val(y)+1, placing a literal separator between successive blocks and none after the final block. It halts at the exact complete frame: input preserved, raw-symbol separated output exact, both delimited descriptor tapes restored to y, input and output heads at their final cursors, both descriptor heads restored. Its total physical clock is at most 8n+floor((n-1)/B)(4w+4)+8w+11, n=|x|, w=|y|. Every return, separator write, final short/full block and saved-template cleanup is included. Natural subtraction covers empty input; empty and arbitrarily padded descriptors are allowed. The fixed finite transition table never receives lengths, numerical block counts or head positions.
-- source:
--   Original actual block-separator service, preserved-output relocation and full caller execution. The checked upload owns all physical service, counter and block proofs. Counter arithmetic and decrement analysis use the pinned Apache-2.0 CrocSwap/integer-mult-bounds source cited in the counted stream. Written by Codex.

import Definitions.Def_IntMul_CountedBlockSplitter
import Definitions.Def_IntMul_BinaryAdder
import Theorems.Thm_IntMul_FiniteCaller_simulate_run
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic

open IntMul.CountedBlockSplitter

theorem IntMul.CountedBlockSplitter.split_blocks (x y : List Bool) :
    ∃ t : ℕ,
      t ≤ 8*x.length+((x.length-1)/blockSize y)*(4*y.length+4)+8*y.length+11 ∧
      machine.step^[t] (machine.initCfg x y)=frame x y x.length none ∧
      (machine.step^[t] (machine.initCfg x y)).state=machine.qHalt := by sorry
