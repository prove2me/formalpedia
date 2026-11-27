-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise52CorrectedXPassageAlmostSureV1
-- name    : Kyprianou.Ch05.exercise52CorrectedXPassageAlmostSureV1
-- status  : Open
-- author  : @jakevej
-- created : 2026-11-27T02:47:25.652251+00:00
-- url     : https://prove2.me/theorems/8fdeaf0a-9c73-5024-a904-0c8ffdbd07aa
-- title:
--   Exercise 5.2 (corrected, a-ii): comparison subordinator crosses every positive level almost surely
-- statement:
--   The comparison subordinator $X$ crosses every positive level almost surely, $P(\tau_x^{X,+}<\infty)=1$. Since the killing rate is $0$, the killing time is literally infinite, so $X$ is unkilled; $F$ is a probability law on $(0,\infty)$, so the Laplace law makes $X$ a compound Poisson subordinator with jump law $F$, whose jumps are almost surely positive and accumulate without bound, and a subordinator is nondecreasing, so it must cross every level.\n\n**Formalization Note** Hypotheses are copied verbatim from the corrected Exercise 5.2 formal statement.
-- source:
--   Kyprianou (2006), first edition, Exercise 5.2 pp.133-134 and author solution pp.322-323; Doney and Kyprianou, Overshoots and undershoots of Levy processes, Ann. Appl. Probab. 16 (2006) 91-106.

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

/-- Exercise 5.2 (corrected), part (a-ii): the comparison subordinator crosses every positive level almost surely. -/
theorem exercise52CorrectedXPassageAlmostSureV1
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
  ∀ x : Real, 0 < x →
      (P {omega : Omega | PassageFinite X deathX x omega}).toReal = 1 := by
  sorry

end Kyprianou.Ch05
