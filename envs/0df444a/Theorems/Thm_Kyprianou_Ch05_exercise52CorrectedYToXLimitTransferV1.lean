-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise52CorrectedYToXLimitTransferV1
-- name    : Kyprianou.Ch05.exercise52CorrectedYToXLimitTransferV1
-- status  : Open
-- author  : @jakevej
-- created : 2026-11-27T02:27:56.664893+00:00
-- url     : https://prove2.me/theorems/141d9564-780c-5f82-9413-950f3a316a2d
-- title:
--   Exercise 5.2 (corrected, ii-a): Y-conditional pair and X joint pair have the same limit
-- statement:
--   Under the same hypotheses as the corrected Exercise 5.2 (ii), the conditional joint overshoot/drawdown law of the risk process $Y$ and the (unconditioned) joint passage law of the comparison subordinator $X$ have the same limit as the level $x\to\infty$: their difference tends to $0$ for every $u,y>0$. This is the Doney-Kyprianou transfer: at large levels the defective ladder renewal of $Y$, normalised by the crossing probability, has the same limit as the unkilled renewal law of $X$. Combined with the already proved comparison limit for $X$ (exercise52ComparisonTailLimitV1), it gives the corrected conditional tail limit for $Y$.\n\n**Formalization Note** Hypotheses are copied verbatim from the corrected Exercise 5.2 (ii) formal statement; the conclusion is the difference of the two Tendsto functions tending to $0$.
-- source:
--   Kyprianou (2006), first edition, Exercise 5.2 pp.133-134 and author solution pp.322-323; Doney and Kyprianou, Overshoots and undershoots of Levy processes, Ann. Appl. Probab. 16 (2006) 91-106; Kluppelberg, Kyprianou and Maller, Ann. Appl. Probab. 14 (2004) 1766-1801.

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

/-- Exercise 5.2 (corrected), part (ii-a): the Y-conditional pair and the X joint pair
have the same limit, so their difference tends to zero. This is the transfer step
that reduces the Y limit to the already proved X comparison limit. -/
theorem exercise52CorrectedYToXLimitTransferV1
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
  (IntegrableOn
       (fun z : Real => z * (triplet.levyMeasure (Set.Ioi z)).toReal)
       (Set.Ioi 0) volume) → ∀ u y : Real, 0 < u → 0 < y →
      Tendsto
        (fun x : Real =>
          conditionalRunningSupremumPair P Y
            (fun _ => (⊤ : WithTop NNReal)) x
            (Set.Ioi u) (Set.Ioi y) -
          (P {omega : Omega |
            PassageFinite X deathX x omega ∧
            passageOvershoot X deathX x omega ∈ Set.Ioi u ∧
            passageUndershoot X Xleft deathX x omega ∈ Set.Ioi y}).toReal)
        atTop (nhds 0) := by
  sorry

end Kyprianou.Ch05
