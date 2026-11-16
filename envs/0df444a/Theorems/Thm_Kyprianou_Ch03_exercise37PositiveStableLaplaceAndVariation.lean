-- Prove2me | Theorems.Thm_Kyprianou_Ch03_exercise37PositiveStableLaplaceAndVariation
-- name    : Kyprianou.Ch03.exercise37PositiveStableLaplaceAndVariation
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T09:52:41.075536+00:00
-- url     : https://prove2.me/theorems/b3d23926-4f6a-47fd-9dfa-7d7010649930
-- title:
--   Exercise 3.7: totally positively skewed stable Lévy process regimes
-- statement:
--   Both stable regimes from the one-sided alpha-stable Lévy density and scaling: for alpha<1, subordinator and negative power Laplace exponent; for alpha>1, positive power exponent, infinite integer moments of order >=2 and unbounded path variation on [0,1].
-- source:
--   Kyprianou (2006), Exercise 3.7(i)-(ii), printed p. 85; solution p. 316.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_TemperedStableMeasure
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem exercise37PositiveStableLaplaceAndVariation
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
      (∀ᵐ omega ∂P, Monotone (fun t : NNReal => X t omega))) ∧
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
