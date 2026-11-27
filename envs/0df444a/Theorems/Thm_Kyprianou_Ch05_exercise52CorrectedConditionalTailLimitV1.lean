-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise52CorrectedConditionalTailLimitV1
-- name    : Kyprianou.Ch05.exercise52CorrectedConditionalTailLimitV1
-- status  : Open
-- author  : @jakevej
-- created : 2026-11-27T02:18:44.512479+00:00
-- url     : https://prove2.me/theorems/90abc55e-d4f7-4286-b0c0-65a942292918
-- title:
--   Exercise 5.2 (corrected, ii): finite-mean limiting conditional joint law
-- statement:
--   Under the finite-mean condition, the conditional joint law of the risk process $Y$ at first passage of a large level $x$ converges: for $u,y>0$,
--
--   $$P(\text{overshoot}>u,\ \text{drawdown from the running maximum}>y \mid \tau_x^+<\infty) \to \frac{\int_{u+y}^{\infty} F((z,\infty))\,dz}{\int z\,F(dz)},$$
--
--   where $F$ is the integrated-tail record jump law. This is part (ii) of the corrected Exercise 5.2. Unlike the false finite-level equality, this limit is the Doney-Kyprianou asymptotic overshoot law: at large levels the defective ladder renewal, normalised by the crossing probability, has the same limit as the unkilled renewal law, which is the key renewal theorem applied to $F$.
--
--   **Formalization Note** Hypotheses are copied verbatim from the original Exercise 5.2 formal statement; the conclusion is its part (ii) with the local $\mathrm{let}$ unfolded, as in the already proved comparison version.
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

/-- Exercise 5.2 (corrected), part (ii): the finite-mean limiting conditional joint overshoot/drawdown law of the risk process. -/
theorem exercise52CorrectedConditionalTailLimitV1
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
            (Set.Ioi u) (Set.Ioi y))
        atTop
        (nhds
          ((∫ z in Set.Ioi (u+y),
              (F (Set.Ioi z)).toReal ∂volume) /
                (∫ z : Real, z ∂F))) := by
  sorry

end Kyprianou.Ch05
