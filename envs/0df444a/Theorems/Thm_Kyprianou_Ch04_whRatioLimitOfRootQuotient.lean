-- Prove2me | Theorems.Thm_Kyprianou_Ch04_whRatioLimitOfRootQuotient
-- name    : Kyprianou.Ch04.whRatioLimitOfRootQuotient
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:26:11.083251+00:00
-- url     : https://prove2.me/theorems/5d1bda2a-8cd4-5212-874f-05ecefc61161
-- title:
--   Wiener-Hopf quotient limit from root quotient
-- statement:
--   Rewrite the Wiener-Hopf quotient so only the root quotient and the discount need to converge. Then apply continuity of division at the nonzero limiting denominator.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.9 and Theorem 4.10

import Mathlib
open Filter Set MeasureTheory
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.whRatioLimitOfRootQuotient
    (q r : ℕ → ℝ)
    (beta m psiBeta : ℝ)
    (hr : ∀ n, 0 < r n)
    (hpsi : psiBeta ≠ 0)
    (hq0 : Tendsto q atTop (nhds 0))
    (hquot : Tendsto (fun n => q n / r n) atTop (nhds m)) :
    Tendsto (fun n => (q n / r n) * ((r n - beta) / (q n - psiBeta)))
      atTop (nhds (m * beta / psiBeta)) := by
  sorry
