-- Prove2me | Theorems.Thm_Malliavin_range_wienerIntegral
-- name    : Malliavin.range_wienerIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:49:53.8538+00:00
-- url     : https://prove2.me/theorems/bff21005-2235-4401-afa1-604b2c2bc293
-- title:
--   Malliavin: range wiener Integral
-- statement:
--   **The first chaos is the range of the Wiener integral.**
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L847-L867
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L847-L867

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.range_wienerIntegral (hB : IsPreBrownianReal B P) :
    LinearMap.range (wienerIntegral hB).toLinearMap = firstChaos hB := by sorry
