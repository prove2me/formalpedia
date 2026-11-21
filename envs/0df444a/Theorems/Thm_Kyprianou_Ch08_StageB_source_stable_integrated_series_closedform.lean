-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_stable_integrated_series_closedform
-- name    : Kyprianou.Ch08.StageB.source_stable_integrated_series_closedform
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T12:38:39.40819+00:00
-- url     : https://prove2.me/theorems/647378d5-ee83-4b36-a106-0e33d000700c
-- title:
--   Stable integrated series geometric closed form
-- statement:
--   Stable scale coefficient geometric series equals its rational closed form. Factor terms using the existing proved factor theorem and sum the geometric ratio.
-- source:
--   Kyprianou (2006), Exercise 8.2

import Mathlib
set_option autoImplicit false

namespace Kyprianou.Ch08.StageB
theorem source_stable_integrated_series_closedform
    (α q β : ℝ) (hα : 1 < α) (hq : 0 < q)
    (hβ : q ^ (1 / α) < β) :
    (β * (β ^ α - q))⁻¹ =
      ∑' n : ℕ, q ^ n * β ^ (-(α * (n + 1) + 1)) := by
  sorry
end Kyprianou.Ch08.StageB
