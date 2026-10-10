-- Prove2me | Theorems.Thm_IntMul_CountedStream_template_reset_correct
-- name    : IntMul.CountedStream.template_reset_correct
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T19:14:12.751662+00:00
-- url     : https://prove2.me/theorems/4ce99cc3-f6e2-499f-bb3e-a0615e2fe561
-- title:
--   Literal saved-template counter reset in 2w+2 transitions
-- statement:
--   For any base configuration and two equal-width binary words of width w, the literal counted-stream machine, started in its resetLeft state with heads on the least significant counter and template cells, is exactly in its halted reset frame after 2w+2 transitions. Both working tapes then contain the original template word between unchanged separators, and both work heads are restored to the original least-significant position. The input and output tapes and their heads are exactly preserved from the arbitrary base configuration. The result includes width zero (adjacent delimiters). This establishes the physical saved-template reset and charges its head returns; full counted-stream setup, payload, and dispatch composition are separate obligations.
-- source:
--   Counter arithmetic and amortized decrement analysis adapted from CrocSwap/integer-mult-bounds at 3b6b66891c0ac888521cf591fe306c6286601d4f, research/machine-transfer-verification/stream-transfer/counters/CounterArithmetic.lean and RippleCounter.lean (Apache-2.0). https://github.com/CrocSwap/integer-mult-bounds/tree/3b6b66891c0ac888521cf591fe306c6286601d4f/research/machine-transfer-verification/stream-transfer/counters . Their README explicitly leaves payload/reset/dispatcher composition outside its cost theorem. This finite table implements those phases in the campaign’s one-sided MultitapeTM model, reversing the counter orientation to fit the big-endian input descriptor. No claim is made of a new counter algorithm.

import Definitions.Def_IntMul_CountedStream
import Mathlib.Data.List.GetD
import Mathlib.Tactic

theorem IntMul.CountedStream.template_reset_correct (base : IntMul.CountedStream.machine.Cfg) (bits template : List Bool)
    (h : bits.length = template.length) :
    IntMul.CountedStream.machine.step^[2 * bits.length + 2]
      (IntMul.CountedStream.resetFrame base .resetLeft bits template (bits.length + 1)) =
        IntMul.CountedStream.resetFrame base .halt template template (template.length + 1) := by sorry
