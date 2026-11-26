-- Prove2me | Theorems.Thm_Malliavin_map_wienerIntegral_eq_gaussianReal
-- name    : Malliavin.map_wienerIntegral_eq_gaussianReal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:53:44.088474+00:00
-- url     : https://prove2.me/theorems/df06b2d1-20bb-5129-a338-2925343c2d19
-- title:
--   Malliavin: map wiener Integral eq gaussian Real
-- statement:
--   **The law of a Wiener integral** is the centered Gaussian with variance `‖f‖²`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L823-L829
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L823-L829

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
open CameronMartin

theorem Malliavin.map_wienerIntegral_eq_gaussianReal (hB : IsPreBrownianReal B P)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    P.map (wienerIntegral hB f) = gaussianReal 0 (‖f‖₊ ^ 2) := by sorry
