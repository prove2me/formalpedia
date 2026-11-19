-- Prove2me | Theorems.Thm_Kyprianou_Ch03_rootSlope_rightSlopeImpliesZero
-- name    : Kyprianou.Ch03.rootSlope_rightSlopeImpliesZero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T15:59:40.596245+00:00
-- url     : https://prove2.me/theorems/47978025-04b4-4bc5-8011-6cf7b3c0e85e
-- title:
--   Chapter 3 zero-root right-slope criterion: reverse implication
-- statement:
--   Prove one direction of the original right-slope criterion for any maximal nonnegative zero of the original Laplace exponent; the source hypotheses and its root are unchanged.
-- source:
--   Kyprianou (2006), Chapter 3, zero-root/right-slope criterion

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem rootSlope_rightSlopeImpliesZero
{Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂P,
      Antitone (fun t : NNReal => L.X t omega))) :
    ∀ (phi : ℝ), (0 ≤ phi ∧ L.ψ phi = 0 ∧ (∀ theta : ℝ, 0 ≤ theta → L.ψ theta = 0 → theta ≤ phi)) →
      (∀ a : ℝ, a < 0 →
          ∃ delta : ℝ, 0 < delta ∧
            ∀ theta : ℝ, 0 < theta → theta < delta →
              a < L.ψ theta / theta) → phi = 0 := by
  sorry

end Kyprianou.Ch03
