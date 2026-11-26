-- Prove2me | Theorems.Thm_Malliavin_integral_wienerIntegral
-- name    : Malliavin.integral_wienerIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:50:20.431862+00:00
-- url     : https://prove2.me/theorems/7fb8c926-0c91-4569-9346-9c10b3ac92ec
-- title:
--   Malliavin: integral wiener Integral
-- statement:
--   Wiener integrals are centered.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L336-L349
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L336-L349

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.integral_wienerIntegral (hB : IsPreBrownianReal B P)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    ∫ ω, wienerIntegral hB f ω ∂P = 0 := by sorry
