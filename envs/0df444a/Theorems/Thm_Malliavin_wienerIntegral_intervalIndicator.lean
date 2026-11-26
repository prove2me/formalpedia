-- Prove2me | Theorems.Thm_Malliavin_wienerIntegral_intervalIndicator
-- name    : Malliavin.wienerIntegral_intervalIndicator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:50:38.044388+00:00
-- url     : https://prove2.me/theorems/a1e39e58-265e-4cfb-a689-85e85168bc2c
-- title:
--   Malliavin: wiener Integral interval Indicator
-- statement:
--   `J₁ (1_{(0, t]}) = B t`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L278-L281
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L278-L281

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.wienerIntegral_intervalIndicator (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    wienerIntegral hB (intervalIndicator t) = brownianLp hB t := by sorry
