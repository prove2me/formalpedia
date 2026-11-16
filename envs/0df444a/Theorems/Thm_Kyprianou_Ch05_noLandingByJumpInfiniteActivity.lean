-- Prove2me | Theorems.Thm_Kyprianou_Ch05_noLandingByJumpInfiniteActivity
-- name    : Kyprianou.Ch05.noLandingByJumpInfiniteActivity
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T09:51:45.985202+00:00
-- url     : https://prove2.me/theorems/0623d5d3-b0b5-4ea0-85bc-1c115bbe6c97
-- title:
--   Lemma 5.8: no exact landing by a jump at infinite activity
-- statement:
--   For all x>0 in an infinite-activity killed subordinator, the event of finite strict first passage with zero overshoot but strictly positive undershoot has probability zero.
-- source:
--   Kyprianou (2006), Chapter 5, result 5.8, first edition, printed pp. 119-125.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- Lemma 5.8, p.121: a positive undershoot cannot accompany zero
overshoot in the infinite-activity case. -/
theorem noLandingByJumpInfiniteActivity
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
    (hInfinite : Pi (Set.Ioi (0 : Real)) = ⊤) :
  ∀ x : Real, 0 < x →
    P {omega : Omega |
      PassageFinite Y death x omega ∧
      passageOvershoot Y death x omega = 0 ∧
      0 < passageUndershoot Y Yleft death x omega} = 0
 := by
  sorry

end Kyprianou.Ch05
