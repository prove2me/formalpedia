-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise52CorrectedConditionalRiskLawV1
-- name    : Kyprianou.Ch05.exercise52CorrectedConditionalRiskLawV1
-- status  : Open
-- author  : @jakevej
-- created : 2026-11-27T02:18:44.25725+00:00
-- url     : https://prove2.me/theorems/6727f7e0-2da0-4215-9e57-1de604746bce
-- title:
--   Exercise 5.2 (corrected): conditional risk limit law and deficit
-- statement:
--   This is the corrected form of Exercise 5.2. The original formal statement also asserted, at every finite level $x$, that the conditional joint law of the risk process $Y$ equals the unconditioned joint law of the comparison subordinator $X$. That finite-level equality is false: for a Cramer-Lundberg process with unit-rate arrivals, unit exponential claims and premium rate $2$, the conditional probability that the historical drawdown equals the reserve is $e^{-x/2}$, while the comparison law gives $e^{-x}$. The correct finite-level law uses the defective ladder renewal measure divided by the crossing probability. What remains true, and is asserted here, is: (a) the risk process crosses every positive level with positive probability and the comparison subordinator crosses almost surely; (ii) under the finite-mean condition the conditional joint overshoot and drawdown tails converge to the integrated tail divided by the mean; (iii) the same limit is the joint law of pre-ruin wealth and deficit. Here $F$ is the integrated-tail record jump law, $m$ its normalising mean, and the conditional law is $\mathrm{conditionalRunningSupremumPair}$.
--
--   **Formalization Note** The hypotheses and the limit and reserve conclusions are copied verbatim from the original formal statement; only the false finite-level equality conjunct has been removed.
-- source:
--   Kyprianou (2006), first edition, Exercise 5.2 pp.133-134 and author solution pp.322-323; Doney and Kyprianou, Overshoots and undershoots of Levy processes, Ann. Appl. Probab. 16 (2006) 91-106; Kluppelberg, Kyprianou and Maller, Ann. Appl. Probab. 14 (2004) 1766-1801. Corrected version: see mission discussion, WillR comment 2026-11-26 on the false finite-level conditional equality.

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

/-- Exercise 5.2 (corrected): the false finite-level conditional equality is dropped. Passage positivity, the finite-mean limiting conditional law, and the reserve/deficit interpretation remain. -/
theorem exercise52CorrectedConditionalRiskLawV1
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
    ((∀ x : Real, 0 < x →
      0 < (P {omega : Omega |
        PassageFinite Y (fun _ => (⊤ : WithTop NNReal)) x omega}).toReal ∧
      (P {omega : Omega | PassageFinite X deathX x omega}).toReal = 1) ∧
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
