-- Prove2me | Theorems.Thm_Kyprianou_Ch05_creepingEquivalenceDensity
-- name    : Kyprianou.Ch05.creepingEquivalenceDensity
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T09:52:07.937623+00:00
-- url     : https://prove2.me/theorems/3356ec44-9d8e-4200-9b2c-ba6fe22f4450
-- title:
--   Theorem 5.9: creeping and continuous potential density
-- statement:
--   For infinite jump intensity, drift d=0 implies zero creeping probability at every x>0. If d>0, U has a strictly positive continuous potential density on (0,infinity) and the exact creeping identity P(X_tau=x)=d*u(x).
-- source:
--   Kyprianou (2006), Chapter 5, result 5.9, first edition, printed pp. 119-125.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- Theorem 5.9, p.122: zero drift excludes creeping; positive drift
gives a strictly positive continuous potential density and creeping formula. -/
theorem creepingEquivalenceDensity
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
    (hInfinite : Pi (Set.Ioi (0 : Real)) = ⊤)
    (U : Real → Measure Real)
    (hPotential : IsKilledPotentialFamily P Y death U) :
  ((d = 0 →
     ∀ x : Real, 0 < x → creepingProbability P Y death x = 0) ∧
   (0 < d →
     ∃ u : Real → Real,
       ContinuousOn u (Set.Ioi (0 : Real)) ∧
       (∀ x : Real, 0 < x → 0 < u x) ∧
       ((U 0).restrict (Set.Ioi (0 : Real)) =
         ((volume : Measure Real).restrict (Set.Ioi (0 : Real))).withDensity
           (fun x : Real => ENNReal.ofReal (u x))) ∧
       (∀ x : Real, 0 < x →
         creepingProbability P Y death x = d * u x)))
 := by
  sorry

end Kyprianou.Ch05
