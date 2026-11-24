-- Prove2me | Theorems.Thm_Kyprianou_Ch03_stableVariation_highIndexLaplaceAndUnboundedVariation
-- name    : Kyprianou.Ch03.stableVariation_highIndexLaplaceAndUnboundedVariation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T13:11:23.191247+00:00
-- url     : https://prove2.me/theorems/a3e812a4-fcb3-4b0a-85df-955a6f2f865c
-- title:
--   Exercise 3.7 part 2: highIndexLaplaceAndUnboundedVariation
-- statement:
--   The full original mathematical subpart 2 of Exercise 3.7, with unchanged hypotheses and source conclusion.
-- source:
--   Kyprianou (2006), Chapter 3, Exercise 3.7, part 2

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_TemperedStableMeasure
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem stableVariation_highIndexLaplaceAndUnboundedVariation
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
    (1 < alpha →
      (∃ C : ℝ, 0 < C ∧
        ∀ theta : ℝ, 0 ≤ theta →
          Real.log (∫ omega,
            Real.exp (-theta * X 1 omega) ∂P) =
              C * theta ^ alpha) ∧
      (∀ n : ℕ, 2 ≤ n →
        ¬ Integrable (fun omega => |X 1 omega| ^ n) P) ∧
      (∀ᵐ omega ∂P, ∀ M : ℝ,
        ∃ n : ℕ, ∃ times : Fin (n + 1) → NNReal,
          times 0 = 0 ∧ times (Fin.last n) ≤ 1 ∧
          (∀ i : Fin n, times i.castSucc < times i.succ) ∧
          M < ∑ i : Fin n,
            |X (times i.succ) omega -
              X (times i.castSucc) omega|)) := by
  sorry

end Kyprianou.Ch03
