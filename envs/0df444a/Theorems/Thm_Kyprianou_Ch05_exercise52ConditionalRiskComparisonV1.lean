-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise52ConditionalRiskComparisonV1
-- name    : Kyprianou.Ch05.exercise52ConditionalRiskComparisonV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T17:06:51.810025+00:00
-- url     : https://prove2.me/theorems/cad6c073-e495-47b3-8f75-6c8c9d08978a
-- title:
--   Exercise 5.2(i): conditional risk record passage law equals the comparison subordinator law
-- statement:
--   Exercise 5.2(i): conditional risk record passage law equals the comparison subordinator law
-- source:
--   Kyprianou (2006), Chapter 5, Exercise 5.2

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch05_RiskConditionalPassage
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

theorem exercise52ConditionalRiskComparisonV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y X Xleft : NNReal → Omega → Real)
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    (hLevy : ProbabilityTheory.IsLevyProcess Y P)
    (hLK : ∀ (t : NNReal) (xi : Real),
      charFun (P.map (Y t)) xi =
        Complex.exp (((t : Real) : Complex) *
          Kyprianou.Ch01.levyTripleExponent triplet xi))
    (hBV : triplet.gaussianVariance = 0 ∧
       (∫⁻ z in Set.Ioo (-1 : Real) 1,
         ENNReal.ofReal |z| ∂triplet.levyMeasure) < ⊤)
    (hPositiveJumps : triplet.levyMeasure (Set.Iio 0) = 0)
    (hDownwardDrift : ∀ᵐ omega : Omega ∂P,
      Tendsto (fun t : NNReal => Y t omega) atTop atBot)
    (m : Real)
    (hM : m =
       ∫ z in Set.Ioi (0 : Real),
         (triplet.levyMeasure (Set.Ioi z)).toReal ∂volume)
    (hMPositive : 0 < m)
    (F : Measure Real)
    (hJumpLaw : F = ascendingRecordJumpDistribution
      triplet.levyMeasure m)
    (deathX : Omega → WithTop NNReal)
    (hX : IsKilledSubordinator P X deathX 0)
    (hXCompoundPoisson : ∀ (t : NNReal) (theta : Real),
        0 ≤ theta →
          (∫ omega, Real.exp (-theta*X t omega) ∂P) =
            Real.exp (-(t : Real) *
              (∫ z in Set.Ioi 0,
                (1-Real.exp (-theta*z)) ∂F)))
    (hLeftX : IsLeftLimitVersion P X Xleft)
    :
  ((∀ x : Real, 0 < x →
      0 < (P {omega : Omega |
        PassageFinite Y (fun _ => (⊤ : WithTop NNReal)) x omega}).toReal ∧
      (P {omega : Omega | PassageFinite X deathX x omega}).toReal = 1) ∧
    (∀ x : Real, 0 < x →
      ∀ A B : Set Real, MeasurableSet A → MeasurableSet B →
        conditionalRunningSupremumPair P Y
          (fun _ => (⊤ : WithTop NNReal)) x A B =
        (P {omega : Omega |
          PassageFinite X deathX x omega ∧
          passageOvershoot X deathX x omega ∈ A ∧
          passageUndershoot X Xleft deathX x omega ∈ B}).toReal)) := by
  sorry

end Kyprianou.Ch05
