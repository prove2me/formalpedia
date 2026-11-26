-- Prove2me | Theorems.Thm_Malliavin_wienerIntegral_wienerIntegralEquiv_symm_apply
-- name    : Malliavin.wienerIntegral_wienerIntegralEquiv_symm_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:11:11.793737+00:00
-- url     : https://prove2.me/theorems/f8a91c8a-05b4-53df-83be-b16289edd90d
-- title:
--   Malliavin: wiener Integral wiener Integral Equiv symm apply
-- statement:
--   Applying the Wiener integral after its inverse on the first chaos recovers the ambient
--   random variable.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/TimeDerivative.lean#L151-L155
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/TimeDerivative.lean#L151-L155

import Definitions.Def_Malliavin_WienerIntegral
import Definitions.Def_Malliavin_FubiniLift
import Definitions.Def_Malliavin_MalliavinDerivative
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_TimeDerivative
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.wienerIntegral_wienerIntegralEquiv_symm_apply (hB : IsPreBrownianReal B P)
    (Z : firstChaos hB) :
    wienerIntegral hB ((wienerIntegralEquiv hB).symm Z) = (Z : RandomL2 P) := by sorry
