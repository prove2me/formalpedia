-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise55_discountedPassageMoment
-- name    : Kyprianou.Ch05.exercise55_discountedPassageMoment
-- status  : Open
-- author  : @WillR
-- created : 2026-11-18T12:42:59.815323+00:00
-- url     : https://prove2.me/theorems/81c3fd59-638d-463f-97a0-f55b7f5c0d6f
-- title:
--   Exercise 5.5 component 1: Discounted first-passage moment including zero-prefactor cases
-- statement:
--   Discounted first-passage moment including zero-prefactor cases. This statement retains the exact original assumptions and the relevant complete conjunct of Exercise 5.5.
-- source:
--   Kyprianou (2006), first edition, Chapter 5, Exercise 5.5, component 1

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
theorem exercise55_discountedPassageMoment
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
  (∀ alpha beta x : Real, 0 ≤ alpha → 0 ≤ beta → 0 < x →
      ((0 < alpha + Phi beta →
        IntegrableOn (fun z : Real => Real.exp (-beta*z))
          (Set.Ioi x) (U alpha) ∧
        exponentialFirstPassageMoment P Y death alpha beta x =
          (alpha + Phi beta) *
            ∫ z in Set.Ioi x, Real.exp (-beta*z) ∂(U alpha)) ∧
       (alpha + Phi beta = 0 →
         (beta = 0 →
            exponentialFirstPassageMoment P Y death alpha beta x =
              (P {omega : Omega | PassageFinite Y death x omega}).toReal) ∧
         (0 < beta →
            exponentialFirstPassageMoment P Y death alpha beta x = 0))))
 := by
  sorry

end Kyprianou.Ch05
