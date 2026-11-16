-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise56StableSubordinatorAllParts
-- name    : Kyprianou.Ch05.exercise56StableSubordinatorAllParts
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T09:58:23.872531+00:00
-- url     : https://prove2.me/theorems/efde7c3d-e197-47b4-bb53-46172556dd4e
-- title:
--   Exercise 5.6: stable subordinator, four complete mathematical parts
-- statement:
--   All four original parts for Phi(theta)=theta^alpha, alpha in (0,1): (i) the Lévy density with positive coefficient 1/(-Gamma(-alpha)); (ii) U density z^(alpha-1)/Gamma(alpha); (iii) exact joint u/y density with alpha*sin(pi alpha)/pi and level-independent distribution of (overshoot/x,undershoot/x), including finite passage; (iv) zero creeping probability.
-- source:
--   Kyprianou (2006), first edition, Exercise 5.6, printed pp.135-136, equation (5.21), worked solution p.325.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- Exercise 5.6, all four parts, in the stable regime 0<alpha<1. -/
theorem exercise56StableSubordinatorAllParts
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
  -- (i) The Lévy measure has the exact positive stable density.
  ((Pi =
      ((volume : Measure Real).restrict (Set.Ioi 0)).withDensity
        (fun z : Real =>
          ENNReal.ofReal (z ^ (-1-alpha) / (-Real.Gamma (-alpha))))) ∧
   -- (ii) The undiscounted potential density is x^(alpha-1)/Gamma(alpha).
   ((U 0) =
      ((volume : Measure Real).restrict (Set.Ioi 0)).withDensity
        (fun z : Real =>
          ENNReal.ofReal (z ^ (alpha-1) / Real.Gamma alpha))) ∧
   -- (iii) The full joint density, and its exact scale invariance.
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
            passageUndershoot Y Yleft death y omega / y)) P)) ∧
   -- (iv) Stable paths cannot creep.
   (∀ x : Real, 0 < x → creepingProbability P Y death x = 0))
 := by
  sorry

end Kyprianou.Ch05
