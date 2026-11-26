-- Prove2me | Theorems.Thm_Malliavin_inner_wienerIntegralEquiv_symm
-- name    : Malliavin.inner_wienerIntegralEquiv_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:20:01.169802+00:00
-- url     : https://prove2.me/theorems/ffcf9e5f-0e99-5049-9e54-b6c4ee26feef
-- title:
--   Malliavin: inner wiener Integral Equiv symm
-- statement:
--   Pairing with `J₁⁻¹` is pairing with `J₁`: `⟪g, J₁⁻¹ Z⟫ = ⟪J₁ g, Z⟫`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/TimeDerivative.lean#L158-L162
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/TimeDerivative.lean#L158-L162

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

theorem Malliavin.inner_wienerIntegralEquiv_symm (hB : IsPreBrownianReal B P)
    (g : Lp ℝ 2 nonnegativeLebesgueMeasure) (Z : firstChaos hB) :
    ⟪g, (wienerIntegralEquiv hB).symm Z⟫_ℝ = ⟪wienerIntegral hB g, (Z : RandomL2 P)⟫_ℝ := by sorry
