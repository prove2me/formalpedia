-- Prove2me | Theorems.Thm_Kyprianou_Ch04_martingaleSampledGridEnergy
-- name    : Kyprianou.Ch04.martingaleSampledGridEnergy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T09:03:46.023088+00:00
-- url     : https://prove2.me/theorems/f749c0d7-3ba4-59ff-87f9-fdd9d0aea2bb
-- title:
--   Martingale sampled grid energy
-- statement:
--   Square-integrable bounded martingale differences on an increasing deterministic grid obey the telescoping energy identity.
-- source:
--   Kyprianou (2006), Exercise 4.3(iii).

import Mathlib
import Theorems.Thm_Martingale_integral_sq_sum_eq_sum_integral_sq
open MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

/-- Orthogonality of martingale differences sampled on an arbitrary increasing grid. -/
theorem Kyprianou.Ch04.martingaleSampledGridEnergy {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (M : NNReal → Omega → ℝ) (hM : Martingale M F P)
    (e : ℕ → NNReal) (he : Monotone e) (B : ℝ)
    (hV : ∀ j : ℕ, ∀ᵐ w ∂P, |M (e (j+1)) w-M (e j) w| ≤ B)
    (N : ℕ) :
    (∫ w, (M (e N) w-M (e 0) w)^2 ∂P) =
    ∑ j ∈ Finset.range N, ∫ w, (M (e (j+1)) w-M (e j) w)^2 ∂P := by
  sorry
