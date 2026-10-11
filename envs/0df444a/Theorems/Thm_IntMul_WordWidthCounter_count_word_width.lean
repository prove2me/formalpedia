-- Prove2me | Theorems.Thm_IntMul_WordWidthCounter_count_word_width
-- name    : IntMul.WordWidthCounter.count_word_width
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T15:13:48.004955+00:00
-- url     : https://prove2.me/theorems/711b0e55-915a-47df-a7a5-08f57a445972
-- title:
--   Physical framed-word width counting with exact logarithmic counter storage
-- statement:
--   Let $w$ be a finite binary source word of length $L$, including the empty word. From the explicit configuration with $w$ on the marked source tape, empty output and counter tapes, and every head at its start marker, the fixed physical counter machine halts in its exact terminal frame within
--
--   $$6L+4$$
--
--   actual transitions. It retains the source and empty output, and writes a little-endian counter $b$ satisfying
--
--   $$\operatorname{val}_{\mathrm{LE}}(b)+1=\max(L,1),\qquad |b|=\left\lceil\log_2(\max(L,1))\right\rceil.$$
--
--   No numerical length is supplied to the machine. Every scan, ripple carry, marker rewind and caller return is charged. This framed-word routine permits an already computed input descriptor to be physically counted, providing a logarithmic block width without a caller-supplied parameter.
-- source:
--   Original complete physical framed-word counting with empty-word behavior, full retained frame and exact logarithmic counter storage. Written by Codex.

import Definitions.Def_IntMul_InputWidthCounter
import Mathlib.Tactic
import Definitions.Def_IntMul_WordWidthCounter

open IntMul IntMul.WordWidthCounter

theorem IntMul.WordWidthCounter.count_word_width (w : List Bool) :
    ∃ t : ℕ, t≤ 6*w.length+4 ∧
      machine.step^[t] (initialFrame w)=finalFrame w ∧
      (machine.step^[t] (initialFrame w)).state=machine.qHalt ∧
      (machine.step^[t] (initialFrame w)).cells machine.inTape=(initialFrame w).cells machine.inTape ∧
      (machine.step^[t] (initialFrame w)).cells machine.outTape=machine.tapeOf [] ∧
      BinaryAdder.littleVal (counterWord w)+1=max w.length 1 ∧
      (counterWord w).length=Nat.clog 2 (max w.length 1) := by sorry
