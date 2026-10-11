-- Prove2me | Theorems.Thm_IntMul_InputWidthCounter_input_width_counter
-- name    : IntMul.InputWidthCounter.input_width_counter
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T14:48:44.394867+00:00
-- url     : https://prove2.me/theorems/98529195-22ff-488c-97f4-88e672f4a986
-- title:
--   Actual input-derived width-minus-one counter from the global initial configuration with linear clock
-- statement:
--   Let $x,y$ be finite binary operand words with $W=|x|+|y|>0$. A fixed three-tape machine starts from the ordinary global initial configuration on $x\#y$, with empty output and work tapes and all heads on their start markers. It physically constructs a little-endian binary counter of value $W-1$ on work tape 2 and halts in its exact complete terminal configuration after at most
--
--   $$6W+4$$
--
--   actual transitions. The original input tape is retained read-only and global output is retained empty. No width word, length, local bank data or counter bits are supplied in advance. Every scanned operand bit, skipped separator, ripple write, blank extension, marker rewind and finite-caller return is charged. The resulting word provides an input-derived descriptor for exact multiplication output width after a separately charged physical order conversion. The theorem covers an empty first operand whenever the second is nonempty.
-- source:
--   Original complete physical input-derived width counting from true global initialization. Owns native increment embedding, per-bit caller frames, all scan/separator/end transitions, opening, first-bit skip, exact terminal frame and linear cost summation. Written by Codex.

import Definitions.Def_IntMul_InputWidthCounter
import Mathlib.Tactic

open IntMul IntMul.InputWidthCounter

theorem IntMul.InputWidthCounter.input_width_counter (x y : List Bool) (hp : 0 < x.length+y.length) :
    ∃ t : ℕ, t ≤ 6*(x.length+y.length)+4 ∧
      machine.step^[t] (initialFrame x y)=finalFrame x y ∧
      (machine.step^[t] (initialFrame x y)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame x y)).cells machine.inTape=(initialFrame x y).cells machine.inTape ∧
      (machine.step^[t] (initialFrame x y)).cells machine.outTape=machine.tapeOf [] ∧
      BinaryAdder.littleVal (GrowingCounter.iterateCounter (x.length+y.length-1) [])+1=x.length+y.length := by sorry
