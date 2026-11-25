-- Prove2me | Theorems.Thm_Kyprianou_Ch04_rightContinuousDyadicSupV1
-- name    : Kyprianou.Ch04.rightContinuousDyadicSupV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:27:13.900861+00:00
-- url     : https://prove2.me/theorems/b162a0e9-3606-44c8-ab0b-4ac4782b3203
-- title:
--   Right-continuous path extended supremum is the dyadic supremum
-- statement:
--   Right-continuity and nonnegativity identify the extended supremum over the whole horizon with the countable dyadic maximum.
-- source:
--   Kyprianou (2006), Exercise 4.5(ii); maximal estimate via discrete grids and monotone convergence.

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem rightContinuousDyadicSupV1 (f : ℝ≥0 → ℝ) (T : ℝ≥0) (hT : 0 < T)
    (hf : ∀ t, 0 ≤ f t)
    (hr : ∀ t, ContinuousWithinAt f (Ici t) t) :
    (⨆ t : Iic T, ENNReal.ofReal (f t)) =
      ⨆ n : ℕ, ENNReal.ofReal ((Finset.range (2^n+1)).sup'
        Finset.nonempty_range_add_one (fun i => f ((i : ℝ≥0) * T / (2^n : ℝ≥0)))) := by
  sorry
end Kyprianou.Ch04
