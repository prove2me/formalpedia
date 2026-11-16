-- Prove2me | Theorems.Thm_Kyprianou_Ch05_finiteMeanPassageJointWeakLimit
-- name    : Kyprianou.Ch05.finiteMeanPassageJointWeakLimit
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T09:51:21.432547+00:00
-- url     : https://prove2.me/theorems/b95fe313-31e0-4927-a877-4d2e14c9da70
-- title:
--   Theorem 5.7: limiting joint overshoot and undershoot including creeping
-- statement:
--   Finite positive mean and nonlattice potential yield weak convergence of the full joint law to the exact jump intensity dy Pi(y+du)/mu plus the creeping atom d/mu at (0,0); the limiting creeping probability d/mu is required separately. Exercise 5.1 must prove this independently.
-- source:
--   Kyprianou (2006), first edition, result 5.7, printed pages 121, 130 or 132.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_WeakPassageObservables
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- Theorem 5.7, p.121: entire finite-mean weak joint law,
including the creeping mass d/mu at (0,0), and its separate limit. -/
theorem finiteMeanPassageJointWeakLimit
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y Yleft : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : IsKilledSubordinator P Y death 0)
    (hTriplet : IsKilledLaplaceTriplet 0 d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * Phi theta))
    (hLeft : IsLeftLimitVersion P Y Yleft)
    (U : Real → Measure Real)
    (hPotential : IsKilledPotentialFamily P Y death U)
    (hFiniteMean : Integrable (Y (1 : NNReal)) P)
    (hPositiveMean : 0 < ∫ omega, Y 1 omega ∂P)
    (hNonLattice : NonLatticeMeasure (U 0)) :
  let mu : Real := ∫ omega, Y 1 omega ∂P
  ((∀ f : Real × Real → Real, IsBoundedContinuousTest f →
     Tendsto
       (fun x : Real => passageTestExpectation P Y Yleft death x f)
       atTop
       (nhds
         (d / mu * f (0,0) +
           (1 / mu) *
             (∫ y in Set.Ici (0 : Real),
                ∫ z in Set.Ioi y, f (z-y,y) ∂Pi ∂volume)))) ∧
   (Tendsto (fun x : Real => creepingProbability P Y death x)
     atTop (nhds (d / mu))))
 := by
  sorry

end Kyprianou.Ch05
