-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise55_creepingDensityBoundary
-- name    : Kyprianou.Ch05.exercise55_creepingDensityBoundary
-- status  : Open
-- author  : @WillR
-- created : 2026-11-18T12:42:45.710809+00:00
-- url     : https://prove2.me/theorems/a9fc06b2-e56d-4d10-989f-efb3ff37446a
-- title:
--   Exercise 5.5 component 3: Creeping, positive potential density and boundary derivative
-- statement:
--   Creeping, positive potential density and boundary derivative. This statement retains the exact original assumptions and the relevant complete conjunct of Exercise 5.5.
-- source:
--   Kyprianou (2006), first edition, Chapter 5, Exercise 5.5, component 3

import Definitions.Def_Kyprianou_Ch05_ExponentialPassageMoments
import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_WeakPassageObservables
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- Exercise 5.5, all four subparts, including equation (5.20). -/
theorem exercise55_creepingDensityBoundary
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y Yleft : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (U : Real → Measure Real)
    (hKilled : IsKilledSubordinator P Y death 0)
    (hTriplet : IsKilledLaplaceTriplet 0 d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * Phi theta))
    (hPotential : IsKilledPotentialFamily P Y death U)
    (hLeft : IsLeftLimitVersion P Y Yleft)
 :
  ((d = 0 →
      ∀ alpha x : Real, 0 ≤ alpha → 0 < x →
        exponentialCreepingMoment P Y death alpha x = 0) ∧
    (0 < d →
      ∀ alpha : Real, 0 ≤ alpha →
        ∃ ualpha : Real → Real,
          ContinuousOn ualpha (Set.Ioi (0 : Real)) ∧
          (∀ x : Real, 0 < x → 0 < ualpha x) ∧
          ((U alpha).restrict (Set.Ioi (0 : Real)) =
            ((volume : Measure Real).restrict (Set.Ioi (0 : Real))).withDensity
               (fun x : Real => ENNReal.ofReal (ualpha x))) ∧
          (∀ x : Real, 0 < x →
            exponentialCreepingMoment P Y death alpha x =
              d * ualpha x) ∧
          Tendsto ualpha
            (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds (1 / d))))
 := by
  sorry

end Kyprianou.Ch05
