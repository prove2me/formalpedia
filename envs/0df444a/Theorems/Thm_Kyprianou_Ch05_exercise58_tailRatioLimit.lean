-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise58_tailRatioLimit
-- name    : Kyprianou.Ch05.exercise58_tailRatioLimit
-- status  : Open
-- author  : @WillR
-- created : 2026-11-18T12:42:15.018277+00:00
-- url     : https://prove2.me/theorems/efe1ade9-3b1a-4506-abc1-57bdbd0dee97
-- title:
--   Exercise 5.8 component 3: Class-L conditional overshoot asymptotic transform
-- statement:
--   Class-L conditional overshoot asymptotic transform. The exact original common killed-subordinator hypotheses and this mathematical clause of the five-part Exercise 5.8 are preserved.
-- source:
--   Kyprianou (2006), first edition, Chapter 5, Exercise 5.8, component 3

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
theorem exercise58_tailRatioLimit
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
  (∀ beta : Real, 0 ≤ beta →
     Tendsto
       (fun x : Real => conditionalOvershootTransform P Y death beta x)
       atTop
       (nhds (if beta = 0 then 1
          else (Phi beta / eta) * (alpha / (alpha+beta)))))
 := by
  sorry

end Kyprianou.Ch05
