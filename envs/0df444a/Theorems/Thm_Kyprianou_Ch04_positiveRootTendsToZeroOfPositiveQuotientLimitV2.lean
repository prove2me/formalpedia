-- Prove2me | Theorems.Thm_Kyprianou_Ch04_positiveRootTendsToZeroOfPositiveQuotientLimitV2
-- name    : Kyprianou.Ch04.positiveRootTendsToZeroOfPositiveQuotientLimitV2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T19:33:57.198641+00:00
-- url     : https://prove2.me/theorems/73e34632-8ab7-5302-aec8-7f051cb33665
-- title:
--   Positive root must vanish when discount tends to zero and quotient has positive limit
-- statement:
--   If positive q_n tends to zero, positive r_n satisfies q_n/r_n tending to strictly positive m, then r_n tends to zero. This is the positive-slope branch of the q/Phi(q) asymptotic for Corollary 4.9.
-- source:
--   Kyprianou (2006), Corollary 4.9, positive-mean root/discount asymptotics.

import Mathlib
open Filter
open scoped Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.positiveRootTendsToZeroOfPositiveQuotientLimitV2
    (q r : ℕ → ℝ) (hq : ∀ n, 0 < q n) (hr : ∀ n, 0 < r n)
    (m : ℝ) (hm : 0 < m)
    (hq0 : Tendsto q atTop (𝓝 0))
    (hquot : Tendsto (fun n => q n / r n) atTop (𝓝 m)) :
    Tendsto r atTop (𝓝 0) := by
  sorry
