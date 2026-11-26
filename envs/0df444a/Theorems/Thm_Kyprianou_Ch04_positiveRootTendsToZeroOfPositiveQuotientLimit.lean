-- Prove2me | Theorems.Thm_Kyprianou_Ch04_positiveRootTendsToZeroOfPositiveQuotientLimit
-- name    : Kyprianou.Ch04.positiveRootTendsToZeroOfPositiveQuotientLimit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T19:26:57.781913+00:00
-- url     : https://prove2.me/theorems/a2122081-e0cf-5829-beb9-c5e7262b1877
-- title:
--   Positive root must vanish when discount tends to zero and quotient has positive limit
-- statement:
--   If positive q_n tends to zero, positive r_n satisfies q_n/r_n tending to strictly positive m, then r_n tends to zero. This is the positive-slope branch of the q/Phi(q) asymptotic for Corollary 4.9.
-- source:
--   Kyprianou (2006), Corollary 4.9, positive-mean root/discount asymptotics.

import Mathlib
open Filter
set_option autoImplicit false

theorem Kyprianou.Ch04.positiveRootTendsToZeroOfPositiveQuotientLimit
    (q r : ℕ → ℝ) (hq : ∀ n, 0 < q n) (hr : ∀ n, 0 < r n)
    (m : ℝ) (hm : 0 < m)
    (hq0 : Tendsto q atTop (nhds 0))
    (hquot : Tendsto (fun n => q n / r n) atTop (nhds m)) :
    Tendsto r atTop (nhds 0) := by
  sorry
