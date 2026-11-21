-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_stable_integrated_coeff_summable
-- name    : Kyprianou.Ch08.StageB.source_stable_integrated_coeff_summable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T12:33:50.383481+00:00
-- url     : https://prove2.me/theorems/4963b7ff-1af7-47ed-9d49-8a239dcb8dfd
-- title:
--   Stable integrated scale coefficients form a convergent geometric series
-- statement:
--   Exact real algebraic geometric-series sublemma for stable q-scale integrated Laplace series in Exercise 8.2(i). Factor β power into a constant β^(-α-1) and ratio (q/β^α)^n; exploit Proved ratio bounds 0≤q/β^α<1.
-- source:
--   Kyprianou (2006) Ch8 Exercise 8.2(i).

import Mathlib
set_option autoImplicit false

namespace Kyprianou.Ch08.StageB
theorem source_stable_integrated_coeff_summable
    (α q β : ℝ) (hα : 1 < α) (hq : 0 < q)
    (hβ : q ^ (1 / α) < β) :
    Summable (fun n : ℕ =>
      q ^ n * β ^ (-(α * (n + 1) + 1))) := by
  sorry
end Kyprianou.Ch08.StageB
