-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedJointPassageKernel
-- name    : Kyprianou.Ch05.killedJointPassageKernel
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T09:50:31.631233+00:00
-- url     : https://prove2.me/theorems/fc56fe42-6321-4099-bf87-f4dcb572ddbe
-- title:
--   Theorem 5.6: complete joint overshoot and undershoot law
-- statement:
--   For an arbitrary killed subordinator, the joint measure of its strictly positive overshoot and nonnegative undershoot on all measurable rectangles is U(x-dy)Pi(y+du), including all endpoints y=0 and y=x. The law excludes creeping exactly by u>0.
-- source:
--   Kyprianou (2006), Chapter 5, result 5.6, first edition, printed pp. 119-125.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- Theorem 5.6, p.119: full joint positive overshoot/undershoot law. -/
theorem killedJointPassageKernel
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y Yleft : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (eta d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : IsKilledSubordinator P Y death eta)
    (hTriplet : IsKilledLaplaceTriplet eta d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * (Phi theta - eta)))
    (hLeft : IsLeftLimitVersion P Y Yleft)
    (U : Real → Measure Real)
    (hPotential : IsKilledPotentialFamily P Y death U) :
  ∀ (x : Real), 0 < x →
    ∀ (A B : Set Real), MeasurableSet A → MeasurableSet B →
      A ⊆ Set.Ioi (0 : Real) → B ⊆ Set.Icc (0 : Real) x →
        positiveJointPassageLaw P Y Yleft death x A B =
          jumpPotentialKernel (U 0) Pi x A B
 := by
  sorry

end Kyprianou.Ch05
