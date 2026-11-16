-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise52SpectrallyPositiveRiskJointLaw
-- name    : Kyprianou.Ch05.exercise52SpectrallyPositiveRiskJointLaw
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T09:56:14.431783+00:00
-- url     : https://prove2.me/theorems/af838675-dbe7-4b20-a0ff-c6f312be24d8
-- title:
--   Exercise 5.2: conditional joint risk overshoot, finite-mean law and deficit
-- statement:
--   All original parts: a negative-drifting spectrally positive BV Levy risk process Y and its independent-jump auxiliary subordinator X with the exact integrated-tail record jump law have equal complete conditional first-passage overshoot/undershoot measures at every x; under finite positive jump mean and nonlattice conditions their positive joint tails converge to the integrated tail divided by mean; finally express that same numerical ruin limit directly as the joint law of pre-ruin wealth and deficit for reserve capital minus Y. The insurance interpretation is transparently a restatement of this substantive probability law.
-- source:
--   Kyprianou (2006), first edition, Exercise 5.2 pp.133-134 and author solution pp.322-323.

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

/-- Exercise 5.2, all three source parts: risk process,
conditional joint law, limiting law and reserve/deficit interpretation. -/
theorem exercise52SpectrallyPositiveRiskJointLaw
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
   let hFiniteSecondMoment : Prop := IntegrableOn
       (fun z : Real => z * (triplet.levyMeasure (Set.Ioi z)).toReal)
       (Set.Ioi 0) volume;
    -- (i) Conditional equality of the entire joint passage law,
   -- with no assumed target equality between the two processes.
   -- Source-implied positive risk passage and almost-sure comparison passage.
   ((∀ x : Real, 0 < x →
      0 < (P {omega : Omega |
        PassageFinite Y (fun _ => (⊤ : WithTop NNReal)) x omega}).toReal ∧
      (P {omega : Omega | PassageFinite X deathX x omega}).toReal = 1) ∧
    -- (i) Source-exact conditional risk law equals unconditioned comparison law.
    (∀ x : Real, 0 < x →
      ∀ A B : Set Real, MeasurableSet A → MeasurableSet B →
        conditionalRunningSupremumPair P Y
          (fun _ => (⊤ : WithTop NNReal)) x A B =
        (P {omega : Omega |
          PassageFinite X deathX x omega ∧
          passageOvershoot X deathX x omega ∈ A ∧
          passageUndershoot X Xleft deathX x omega ∈ B}).toReal) ∧
    -- (ii) The full finite-mean limiting joint overshoot and undershoot.
    (hFiniteSecondMoment → ∀ u y : Real, 0 < u → 0 < y →
      Tendsto
        (fun x : Real =>
          conditionalRunningSupremumPair P Y
            (fun _ => (⊤ : WithTop NNReal)) x
            (Set.Ioi u) (Set.Ioi y))
        atTop
        (nhds
          ((∫ z in Set.Ioi (u+y),
              (F (Set.Ioi z)).toReal ∂volume) /
                (∫ z : Real, z ∂F)))) ∧
    -- (iii) Historical minimum reserve, based on the running maximum of Y,
    -- distinguished from the current pre-ruin reserve.
    (hFiniteSecondMoment → ∀ deficit wealth : Real, 0 < deficit → 0 < wealth →
      Tendsto
        (fun capital : Real =>
          (P {omega : Omega |
             PassageFinite Y (fun _ => (⊤ : WithTop NNReal)) capital omega ∧
             deficit <
               Y (passageFiniteTime Y
                   (fun _ => (⊤ : WithTop NNReal)) capital omega) omega -
                 capital ∧
             wealth <
               capital - runningSupremumBefore Y (passageFiniteTime Y
                 (fun _ => (⊤ : WithTop NNReal)) capital omega) omega}).toReal /
          (P {omega : Omega |
             PassageFinite Y
               (fun _ => (⊤ : WithTop NNReal)) capital omega}).toReal)
        atTop
        (nhds
           ((∫ z in Set.Ioi (deficit+wealth),
               (F (Set.Ioi z)).toReal ∂volume) /
               (∫ z : Real, z ∂F)))))
 := by
  sorry

end Kyprianou.Ch05
