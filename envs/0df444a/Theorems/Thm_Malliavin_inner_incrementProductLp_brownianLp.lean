-- Prove2me | Theorems.Thm_Malliavin_inner_incrementProductLp_brownianLp
-- name    : Malliavin.inner_incrementProductLp_brownianLp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:52:58.466255+00:00
-- url     : https://prove2.me/theorems/317fbdfe-d91e-44f7-9ad5-ce5691943b05
-- title:
--   Malliavin: inner increment Product Lp brownian Lp
-- statement:
--   Products of increments are orthogonal to the Brownian coordinates.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L656-L662
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L656-L662

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.inner_incrementProductLp_brownianLp (hB : IsPreBrownianReal B P) (a b c d t : ℝ≥0) :
    ⟪incrementProductLp hB a b c d, brownianLp hB t⟫_ℝ = 0 := by sorry
