-- Prove2me | Theorems.Thm_IntMul_CountedRouter_counted_blocks
-- name    : IntMul.CountedRouter.counted_blocks
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T19:50:52.659704+00:00
-- url     : https://prove2.me/theorems/8c3a41ec-922d-4a02-a94c-dc6d848c6585
-- title:
--   A literal reusable counted-block router: one setup, arbitrary input, and final cleanup
-- statement:
--   For every binary payload x and descriptor y, a single fixed four-tape, five-symbol, 27-state machine copies all of x and halts. It initializes the descriptor once, runs repeated B=val(y)+1-sized blocks with charged dispatch transitions, handles the short final block, and physically restores both delimited descriptor tapes and work heads before global halt. The exact full terminal configuration is proved. With n=|x|, w=|y|, its time is at most 8n+floor((n-1)/B)(4w+3)+8w+11, using natural subtraction for n=0. Arbitrarily padded descriptors and empty input/descriptor words are included; no w≤B assumption is made. The transition table sees only finite state and scanned symbols, never n, w, B, or positions. This gives an actual reusable contiguous-block routing primitive; arbitrary indexed routing and the recursive multiplication scheduler remain separate obligations.
-- source:
--   Counter arithmetic and amortized decrement analysis adapted from CrocSwap/integer-mult-bounds at 3b6b66891c0ac888521cf591fe306c6286601d4f, research/machine-transfer-verification/stream-transfer/counters/CounterArithmetic.lean and RippleCounter.lean (Apache-2.0). https://github.com/CrocSwap/integer-mult-bounds/tree/3b6b66891c0ac888521cf591fe306c6286601d4f/research/machine-transfer-verification/stream-transfer/counters . This proof implements payload/reset/dispatcher composition and repeated calls in the campaign's one-sided MultitapeTM model, with a finite caller compiler and no repeated full-input setup. Written by Codex.

import Definitions.Def_IntMul_CountedRouter
import Theorems.Thm_IntMul_FiniteCaller_simulate_run
import Theorems.Thm_IntMul_CountedStream_template_reset_correct
import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic

open IntMul.CountedRouter

theorem IntMul.CountedRouter.counted_blocks (x y : List Bool) :
    ∃ t : ℕ,
      t ≤ 8 * x.length + ((x.length - 1) / (IntMul.val y + 1)) * (4 * y.length + 3) +
        8 * y.length + 11 ∧
      machine.HaltsWithOutput x y t x ∧
      machine.step^[t] (machine.initCfg x y) = frame x y x.length none := by sorry
