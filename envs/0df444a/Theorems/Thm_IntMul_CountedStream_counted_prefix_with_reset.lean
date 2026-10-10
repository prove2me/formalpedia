-- Prove2me | Theorems.Thm_IntMul_CountedStream_counted_prefix_with_reset
-- name    : IntMul.CountedStream.counted_prefix_with_reset
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T19:30:56.234604+00:00
-- url     : https://prove2.me/theorems/030d3659-e34a-487b-8279-299aba076d26
-- title:
--   A complete literal counted stream with payload, dispatch, and counter reset
-- statement:
--   For every binary input word x and binary descriptor y with B=val(y)+1 ≤ |x|, the fixed thirteen-state, four-tape machine outputs exactly the first B bits of x and halts after at most 2|x|+6B+6|y|+7 actual transitions. It restores both countdown and saved-template tapes to the original y word, with both work heads on their least-significant positions. Every setup scan, saved copy, delimiter write, payload emission, physical decrement and head return, dispatch, saved-template reset, and reset head return is charged. No condition |y|≤B is assumed, so leading-zero padding of the descriptor is explicitly paid for. Width-zero y is included and represents a one-item block. This is a concrete stream/routing primitive, not a full multiplication-machine or campaign-root proof.
-- source:
--   Counter arithmetic and amortized decrement analysis adapted from CrocSwap/integer-mult-bounds at 3b6b66891c0ac888521cf591fe306c6286601d4f, research/machine-transfer-verification/stream-transfer/counters/CounterArithmetic.lean and RippleCounter.lean (Apache-2.0). https://github.com/CrocSwap/integer-mult-bounds/tree/3b6b66891c0ac888521cf591fe306c6286601d4f/research/machine-transfer-verification/stream-transfer/counters . Their README explicitly leaves payload/reset/dispatcher composition outside its cost theorem. This finite table implements those phases in the campaign’s one-sided MultitapeTM model, reversing the counter orientation to fit the big-endian input descriptor. No claim is made of a new counter algorithm.

import Definitions.Def_IntMul_CountedStream
import Theorems.Thm_IntMul_CountedStream_template_reset_correct
import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic

open IntMul.CountedStream
open IntMul.TapeCopy (Sym)

theorem IntMul.CountedStream.counted_prefix_with_reset (x y : List Bool) (hx : IntMul.val y + 1 ≤ x.length) :
    ∃ t : ℕ, t ≤ 2 * x.length + 6 * (IntMul.val y + 1) + 6 * y.length + 7 ∧
      machine.HaltsWithOutput x y t (x.take (IntMul.val y + 1)) ∧
      (machine.step^[t] (machine.initCfg x y)).cells 2 =
        machine.tapeOf (Sym.sep :: (y.map machine.bitSym ++ [Sym.sep])) ∧
      (machine.step^[t] (machine.initCfg x y)).cells 3 =
        machine.tapeOf (Sym.sep :: (y.map machine.bitSym ++ [Sym.sep])) ∧
      (machine.step^[t] (machine.initCfg x y)).head 2 = y.length + 1 ∧
      (machine.step^[t] (machine.initCfg x y)).head 3 = y.length + 1 := by sorry
