-- Prove2me | Theorems.Thm_Kyprianou_Ch05_reciprocalRegularVariationFactor
-- name    : Kyprianou.Ch05.reciprocalRegularVariationFactor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:38:17.707447+00:00
-- url     : https://prove2.me/theorems/f3e2d42f-5963-5ac6-945f-7f5150317981
-- title:
--   Reciprocal regular-variation factor under inversion of the argument
-- statement:
--   Reciprocal regular-variation factor under inversion of the argument
-- source:
--   Kyprianou (2006), Lemma 5.17 and Karamata's theorem, corrected reciprocal factor.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_MonotoneDensity
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.reciprocalRegularVariationFactor
    (Phi : Real → Real) (rho : Real) (l l' : Filter Real)
    (hpos : ∀ x : Real, 0 < x → 0 < Phi x)
    (he : ∀ᶠ x in l, 0 < x)
    (hi : Tendsto (fun x : Real => x⁻¹) l l')
    (hr : ∀ a : Real, 0 < a → Tendsto
      (fun x : Real => Phi (a*x)/Phi x) l' (nhds (a^rho))) :
    ∃ L : Real → Real,
      (∀ x : Real, 0 < x → 0 < L x) ∧
      (∀ x : Real, 0 < x → Phi (1/x) = x^(-rho)/L x) ∧
      ∀ a : Real, 0 < a → Tendsto (fun x : Real => L (a*x)/L x) l (nhds 1) := by sorry
