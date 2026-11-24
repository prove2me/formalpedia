-- Prove2me | Theorems.Thm_Kyprianou_Ch03_stableVariation_lowIndexLaplaceAndMonotone
-- name    : Kyprianou.Ch03.stableVariation_lowIndexLaplaceAndMonotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T13:11:32.874553+00:00
-- url     : https://prove2.me/theorems/d37f36bc-d7cd-4df7-83a4-ef4337f60740
-- title:
--   Exercise 3.7 part 1: lowIndexLaplaceAndMonotone
-- statement:
--   The full original mathematical subpart 1 of Exercise 3.7, with unchanged hypotheses and source conclusion.
-- source:
--   Kyprianou (2006), Chapter 3, Exercise 3.7, part 1

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_TemperedStableMeasure
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem stableVariation_lowIndexLaplaceAndMonotone
{Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : ∀ (t : NNReal) (xi : ℝ),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : ℝ) : ℂ) *
          Kyprianou.Ch01.levyTripleExponent T xi))
    (alpha c : ℝ) (hAlpha : 0 < alpha ∧ alpha < 2)
    (hC : 0 < c) (hGaussian : T.gaussianVariance = 0)
    (hMeasure : T.levyMeasure =
      temperedStablePositiveMeasure c alpha 0)
    (hStable : ∀ (t : NNReal) (scale : ℝ), 0 < scale →
      P.map (X (t * Real.toNNReal scale)) =
        P.map (fun omega => scale ^ (1 / alpha) * X t omega)) :
    (alpha < 1 →
      (∃ C : ℝ, 0 < C ∧
        (∀ theta : ℝ, 0 ≤ theta →
          Real.log (∫ omega,
            Real.exp (-theta * X 1 omega) ∂P) =
              -C * theta ^ alpha)) ∧
      (∀ᵐ omega ∂P, Monotone (fun t : NNReal => X t omega))) := by
  sorry

end Kyprianou.Ch03
