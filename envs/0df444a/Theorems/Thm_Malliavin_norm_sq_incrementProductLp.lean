-- Prove2me | Theorems.Thm_Malliavin_norm_sq_incrementProductLp
-- name    : Malliavin.norm_sq_incrementProductLp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:51:00.641662+00:00
-- url     : https://prove2.me/theorems/fd612f17-ba36-502c-8fd1-bd08888b9ef4
-- title:
--   Malliavin: norm sq increment Product Lp
-- statement:
--   Squared norm of a product of two consecutive disjoint Brownian increments.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L728-L746
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L728-L746

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.norm_sq_incrementProductLp (hB : IsPreBrownianReal B P) {a b c d : ℝ≥0} (hab : a ≤ b)
    (hbc : b ≤ c) (hcd : c ≤ d) :
    ‖incrementProductLp hB a b c d‖ ^ 2 = ((b : ℝ) - a) * ((d : ℝ) - c) := by sorry
