-- Prove2me | Theorems.Thm_Kyprianou_Ch03_upwardPassageZeroRootRightSlopeCriterion
-- name    : Kyprianou.Ch03.upwardPassageZeroRootRightSlopeCriterion
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T09:48:27.039208+00:00
-- url     : https://prove2.me/theorems/c4449b08-47c7-4fb3-894a-37e8d92b0e63
-- title:
--   Corollary 3.13: right derivative criterion including negative infinite mean
-- statement:
--   Phi(0)=0 precisely when the right slope of psi at zero is nonnegative, expressed by an epsilon criterion that also detects an extended value of minus infinity. No integrability of X_1 is assumed.
-- source:
--   Kyprianou (2006), Corollary 3.13 and Exercise 3.5, printed pp. 82, 84 and solution p. 315.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem upwardPassageZeroRootRightSlopeCriterion
{Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂P,
      Antitone (fun t : NNReal => L.X t omega))) :
    ∃ phi : ℝ,
      0 ≤ phi ∧ L.ψ phi = 0 ∧
      (∀ theta : ℝ, 0 ≤ theta → L.ψ theta = 0 → theta ≤ phi) ∧
      (phi = 0 ↔
        ∀ a : ℝ, a < 0 →
          ∃ delta : ℝ, 0 < delta ∧
            ∀ theta : ℝ, 0 < theta → theta < delta →
              a < L.ψ theta / theta) := by
  sorry

end Kyprianou.Ch03
