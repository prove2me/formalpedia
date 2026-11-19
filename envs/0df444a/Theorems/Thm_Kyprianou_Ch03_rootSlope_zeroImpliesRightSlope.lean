-- Prove2me | Theorems.Thm_Kyprianou_Ch03_rootSlope_zeroImpliesRightSlope
-- name    : Kyprianou.Ch03.rootSlope_zeroImpliesRightSlope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T15:59:42.549622+00:00
-- url     : https://prove2.me/theorems/dd5ce7f1-90a9-4496-8a3b-fb5f2039201c
-- title:
--   Chapter 3 zero-root right-slope criterion: forward implication
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

theorem rootSlope_zeroImpliesRightSlope
{Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂P,
      Antitone (fun t : NNReal => L.X t omega))) :
    ∀ (phi : ℝ), (0 ≤ phi ∧ L.ψ phi = 0 ∧ (∀ theta : ℝ, 0 ≤ theta → L.ψ theta = 0 → theta ≤ phi)) →
      phi = 0 → (∀ a : ℝ, a < 0 →
          ∃ delta : ℝ, 0 < delta ∧
            ∀ theta : ℝ, 0 < theta → theta < delta →
              a < L.ψ theta / theta) := by
  sorry

end Kyprianou.Ch03
