-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_stable_integrated_term_factor
-- name    : Kyprianou.Ch08.StageB.source_stable_integrated_term_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T12:33:50.119561+00:00
-- url     : https://prove2.me/theorems/dda9c34f-2210-4ad4-ad0c-5cdd03a9135d
-- title:
--   Stable integrated scale reciprocal-power term factors geometrically
-- statement:
--   Exact real algebraic geometric-series sublemma for stable q-scale integrated Laplace series in Exercise 8.2(i). Factor β power into a constant β^(-α-1) and ratio (q/β^α)^n; exploit Proved ratio bounds 0≤q/β^α<1.
-- source:
--   Kyprianou (2006) Ch8 Exercise 8.2(i).

import Mathlib
set_option autoImplicit false

namespace Kyprianou.Ch08.StageB
theorem source_stable_integrated_term_factor (α q β : ℝ) (hβ : 0 < β) :
    ∀ n : ℕ,
      q ^ n * β ^ (-(α * ((n : ℝ) + 1) + 1)) =
        β ^ (-(α + 1)) * (q / β ^ α) ^ n := by
  sorry
end Kyprianou.Ch08.StageB
