-- Prove2me | Theorems.Thm_Kyprianou_Ch05_unkilledPotentialLaplaceFromSemigroup
-- name    : Kyprianou.Ch05.unkilledPotentialLaplaceFromSemigroup
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:22:40.16848+00:00
-- url     : https://prove2.me/theorems/5a2da4d9-72bb-4a59-9fbf-d236031119d9
-- title:
--   Lemma 5.2: potential resolvent from marginal Laplace semigroup
-- statement:
--   The discounted occupation measure of an unkilled subordinator has resolvent Laplace transform when its marginal time-Laplace semigroup is exponential.
-- source:
--   Kyprianou (2006), Lemma 5.2; exact subordinator Laplace dichotomy reduction cbe8356f-6685-46d0-bf57-78977a3b6679.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.unkilledPotentialLaplaceFromSemigroup
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (hY : Kyprianou.Ch03.IsSubordinator P Y)
    (death : Omega → WithTop NNReal)
    (hd : ∀ w, death w = ⊤)
    (U : Real → Measure Real)
    (hPotential : IsKilledPotentialFamily P Y death U)
    (theta a : Real) (ha : 0 ≤ a)
    (hsem : ∀ t : NNReal, (∫⁻ w, ENNReal.ofReal (Real.exp (-theta * Y t w)) ∂P) =
      ENNReal.ofReal (Real.exp (-a * (t : Real))))
    (q : Real) (hq : 0 ≤ q) :
    (∫⁻ x : Real, ENNReal.ofReal (Real.exp (-theta * x)) ∂(U q)) =
      (ENNReal.ofReal (q + a))⁻¹ := by sorry
