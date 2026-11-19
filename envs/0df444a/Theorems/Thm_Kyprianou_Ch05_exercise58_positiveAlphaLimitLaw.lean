-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise58_positiveAlphaLimitLaw
-- name    : Kyprianou.Ch05.exercise58_positiveAlphaLimitLaw
-- status  : Open
-- author  : @WillR
-- created : 2026-11-18T12:42:06.97322+00:00
-- url     : https://prove2.me/theorems/5e089520-5557-4683-a332-e721de5b6d6a
-- title:
--   Exercise 5.8 component 4: Positive-index limiting probability law and creeping atom
-- statement:
--   Positive-index limiting probability law and creeping atom. The exact original common killed-subordinator hypotheses and this mathematical clause of the five-part Exercise 5.8 are preserved.
-- source:
--   Kyprianou (2006), first edition, Chapter 5, Exercise 5.8, component 4

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_TailRatioClassL
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- Exercise 5.8, full five parts including the alpha=0 escape case. -/
theorem exercise58_positiveAlphaLimitLaw
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (eta d alpha : Real) (Pi : Measure Real)
    (Phi : Real → Real) (U : Real → Measure Real)
    (hEta : 0 < eta)
    (hKilled : IsKilledSubordinator P Y death eta)
    (hTriplet : IsKilledLaplaceTriplet eta d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
         Real.exp (-(t : Real) * (Phi theta-eta)))
    (hPotential : IsKilledPotentialFamily P Y death U)
    (hClassL : IsTailRatioClassL (U 0) alpha)
    (hExtMoment : IntegrableOn
      (fun z : Real => Real.exp (alpha*z)-1) (Set.Ioi 0) Pi)
    (hExtendedPhi : Phi (-alpha) = eta-d*alpha +
      ∫ z in Set.Ioi (0 : Real),
         (1-Real.exp (alpha*z)) ∂Pi)
 :
  (0 < alpha →
     ∃ G : Measure Real, IsProbabilityMeasure G ∧
       G (Set.Iio (0 : Real)) = 0 ∧
       G {0} = ENNReal.ofReal (d*alpha/eta) ∧
       (∀ u : Real, 0 ≤ u →
         (G (Set.Ioi u)).toReal =
           limitingKilledOvershootTail eta alpha Phi Pi u) ∧
       (∀ beta : Real, 0 ≤ beta →
         ∫ z in Set.Ioi (0 : Real),
           Real.exp (-beta*z) ∂G =
           (alpha*Phi beta / (eta*(alpha+beta))) -
              d*alpha/eta) ∧
       (∀ u : Real, 0 ≤ u →
         Tendsto
           (fun x : Real =>
             (P {omega : Omega |
               PassageFinite Y death x omega ∧
               u < passageOvershoot Y death x omega}).toReal /
                 (P {omega : Omega |
                   PassageFinite Y death x omega}).toReal)
           atTop (nhds ((G (Set.Ioi u)).toReal))) ∧
       Tendsto
         (fun x : Real =>
           (P {omega : Omega |
             PassageFinite Y death x omega ∧
             passageOvershoot Y death x omega = 0}).toReal /
             (P {omega : Omega |
                 PassageFinite Y death x omega}).toReal)
         atTop (nhds (d*alpha/eta)))
 := by
  sorry

end Kyprianou.Ch05
