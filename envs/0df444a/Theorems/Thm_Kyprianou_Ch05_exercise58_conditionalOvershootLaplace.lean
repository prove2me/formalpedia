-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise58_conditionalOvershootLaplace
-- name    : Kyprianou.Ch05.exercise58_conditionalOvershootLaplace
-- status  : Open
-- author  : @WillR
-- created : 2026-11-18T12:42:09.367684+00:00
-- url     : https://prove2.me/theorems/4b105e64-46f6-44af-9d24-65ac9e5edb7a
-- title:
--   Exercise 5.8 component 2: Conditional finite-level overshoot transform
-- statement:
--   Conditional finite-level overshoot transform. The exact original common killed-subordinator hypotheses and this mathematical clause of the five-part Exercise 5.8 are preserved.
-- source:
--   Kyprianou (2006), first edition, Chapter 5, Exercise 5.8, component 2

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
theorem exercise58_conditionalOvershootLaplace
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
  (∀ beta x : Real, 0 ≤ beta → 0 ≤ x →
     conditionalOvershootTransform P Y death beta x =
       Phi beta / (eta * (U 0 (Set.Ioi x)).toReal) *
         (∫ z in Set.Ioi x, Real.exp (-beta*(z-x)) ∂(U 0)))
 := by
  sorry

end Kyprianou.Ch05
