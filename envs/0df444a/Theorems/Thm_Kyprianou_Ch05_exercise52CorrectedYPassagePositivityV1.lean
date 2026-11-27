-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise52CorrectedYPassagePositivityV1
-- name    : Kyprianou.Ch05.exercise52CorrectedYPassagePositivityV1
-- status  : Open
-- author  : @jakevej
-- created : 2026-11-27T02:47:20.945651+00:00
-- url     : https://prove2.me/theorems/ba0b054e-1254-51c1-ab44-bf575cbde76a
-- title:
--   Exercise 5.2 (corrected, a-i): risk process crosses every positive level with positive probability
-- statement:
--   For the spectrally positive, bounded-variation Levy risk process $Y$ drifting to $-\infty$, with $m>0$ the integrated Levy tail, every positive level $x$ is crossed with positive probability, $P(\tau_x^+<\infty)>0$. The argument is a single large jump: $m>0$ forces positive Levy jump mass above some level, so in a short time window enough jumps can occur, with positive probability, to cross any $x$ before the negative drift pulls the process down.\n\n**Formalization Note** Hypotheses are copied verbatim from the corrected Exercise 5.2 formal statement.
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

/-- Exercise 5.2 (corrected), part (a-i): the risk process crosses every positive level with positive probability. -/
theorem exercise52CorrectedYPassagePositivityV1
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
      0 < (P {omega : Omega |
        PassageFinite Y (fun _ => (⊤ : WithTop NNReal)) x omega}).toReal := by
  sorry

end Kyprianou.Ch05
