-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise56_jointLawScaleInvariance
-- name    : Kyprianou.Ch05.exercise56_jointLawScaleInvariance
-- status  : Open
-- author  : @WillR
-- created : 2026-11-18T12:41:24.094472+00:00
-- url     : https://prove2.me/theorems/7a34ec51-cbe5-4947-abe7-83dc471f1d57
-- title:
--   Exercise 5.6 part 3: Stable joint passage density and scale invariance
-- statement:
--   Stable joint passage density and scale invariance. Exact original quantified hypotheses and the corresponding mathematical clause of Kyprianou (2006), Chapter 5 Exercise 5.6.
-- source:
--   Kyprianou (2006), first edition, Chapter 5, Exercise 5.6, part 3

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- Exercise 5.6, all four parts, in the stable regime 0<alpha<1. -/
theorem exercise56_jointLawScaleInvariance
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y Yleft : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (U : Real → Measure Real)
    (alpha : Real) (hAlpha : 0 < alpha ∧ alpha < 1)
    (hKilled : IsKilledSubordinator P Y death 0)
    (hTriplet : IsKilledLaplaceTriplet 0 d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * Phi theta))
    (hStablePhi : ∀ theta : Real, 0 ≤ theta → Phi theta = theta ^ alpha)
    (hPotential : IsKilledPotentialFamily P Y death U)
    (hLeft : IsLeftLimitVersion P Y Yleft) :
  ((∀ x : Real, 0 < x →
      ∀ (A B : Set Real), MeasurableSet A → MeasurableSet B →
        A ⊆ Set.Ioi 0 → B ⊆ Set.Ioc 0 x →
          positiveJointPassageLaw P Y Yleft death x A B =
            ∫⁻ u in A,
              (∫⁻ y in B,
                ENNReal.ofReal
                  ((alpha * Real.sin (Real.pi*alpha) / Real.pi) *
                    (x-y) ^ (alpha-1) * (y+u) ^ (-1-alpha))
                  ∂volume) ∂volume) ∧
     (∀ x : Real, 0 < x →
       P {omega : Omega | PassageFinite Y death x omega} = 1) ∧
     (∀ x y : Real, 0 < x → 0 < y →
       Measure.map
         (fun omega : Omega =>
           (passageOvershoot Y death x omega / x,
            passageUndershoot Y Yleft death x omega / x)) P =
       Measure.map
         (fun omega : Omega =>
           (passageOvershoot Y death y omega / y,
            passageUndershoot Y Yleft death y omega / y)) P))
 := by
  sorry

end Kyprianou.Ch05
