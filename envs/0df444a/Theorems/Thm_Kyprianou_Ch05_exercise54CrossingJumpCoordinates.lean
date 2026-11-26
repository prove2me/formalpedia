-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise54CrossingJumpCoordinates
-- name    : Kyprianou.Ch05.exercise54CrossingJumpCoordinates
-- status  : Open
-- author  : @Cloud 
-- created : 2026-11-26T03:10:41.996887+00:00
-- url     : https://prove2.me/theorems/c3148bb2-fc21-52c5-acd5-0df7568a755c
-- title:
--   Exercise 5.4: crossing-jump coordinates at the passage time
-- statement:
--   For almost every path $\omega$ at which the first strict passage time $\tau$ of $Y$ over $x>0$ is finite and the overshoot $Y_\tau-x$ is positive, the left limit satisfies $Y_{\tau-}\le x<Y_\tau$, and the overshoot decomposes through the jump at $\tau$ as $Y_\tau-x = (Y_{\tau-} + (Y_\tau-Y_{\tau-})) - x$. In particular a positive overshoot forces the crossing to occur by a jump whose $Y$-component carries the pre-jump position from at most $x$ to strictly above $x$. This is the coordinate step feeding the compensation identity of Exercise 5.4.
-- source:
--   Kyprianou (2006), first edition, Exercise 5.4, pp.134-135 and worked solution on p.324.

import Mathlib
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_BivariateKilledSubordinator
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05


theorem exercise54CrossingJumpCoordinates
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X Y Xleft Yleft : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (eta dX dY : Real)
    (Pi U : Measure (Real × Real))
    (hBivariate : IsKilledBivariateSubordinator P X Y death eta dX dY Pi)
    (hPotential : IsBivariateKilledPotential P X Y death U)
    (hLeftX : IsLeftLimitVersion P X Xleft)
    (hLeftY : IsLeftLimitVersion P Y Yleft) :
  ∀ x : Real, 0 < x →
    ∀ᵐ omega : Omega ∂P,
      PassageFinite Y death x omega →
      0 < Y (passageFiniteTime Y death x omega) omega - x →
      Yleft (passageFiniteTime Y death x omega) omega ≤ x ∧
      x < Y (passageFiniteTime Y death x omega) omega ∧
      (Y (passageFiniteTime Y death x omega) omega - x) =
        (Yleft (passageFiniteTime Y death x omega) omega +
          (Y (passageFiniteTime Y death x omega) omega -
            Yleft (passageFiniteTime Y death x omega) omega)) - x
 := by
  sorry

end Kyprianou.Ch05
