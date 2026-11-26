-- Prove2me | Theorems.Thm_Malliavin_brownianLp_zero
-- name    : Malliavin.brownianLp_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:54:10.172622+00:00
-- url     : https://prove2.me/theorems/5179c35d-d756-47fd-854e-bfe0a73b9501
-- title:
--   Malliavin: brownian Lp zero
-- statement:
--   `B 0 = 0` in `L²(P)`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L1066-L1070
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L1066-L1070

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.brownianLp_zero (hB : IsPreBrownianReal B P) : brownianLp hB 0 = 0 := by sorry
