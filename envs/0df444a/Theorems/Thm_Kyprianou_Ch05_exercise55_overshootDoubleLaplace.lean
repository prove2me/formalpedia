-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise55_overshootDoubleLaplace
-- name    : Kyprianou.Ch05.exercise55_overshootDoubleLaplace
-- status  : Open
-- author  : @WillR
-- created : 2026-11-18T12:42:44.820219+00:00
-- url     : https://prove2.me/theorems/262944d8-ba33-4935-bc51-ef69c32e58d6
-- title:
--   Exercise 5.5 component 2: Positive-denominator overshoot transform including zero cases
-- statement:
--   Positive-denominator overshoot transform including zero cases. This statement retains the exact original assumptions and the relevant complete conjunct of Exercise 5.5.
-- source:
--   Kyprianou (2006), first edition, Chapter 5, Exercise 5.5, component 2

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
theorem exercise55_overshootDoubleLaplace
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
  (∀ alpha beta q : Real, 0 ≤ alpha → 0 ≤ beta → beta < q →
      ((0 < alpha + Phi q →
        (∫ x in Set.Ioi (0 : Real),
           Real.exp (-q*x) *
             exponentialOvershootMoment P Y death alpha beta x ∂volume) =
          (1 - (alpha + Phi beta) / (alpha + Phi q)) / (q-beta)) ∧
       (alpha + Phi q = 0 →
        (∫ x in Set.Ioi (0 : Real),
           Real.exp (-q*x) *
             exponentialOvershootMoment P Y death alpha beta x ∂volume) = 0)))
 := by
  sorry

end Kyprianou.Ch05
