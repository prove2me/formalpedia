-- Prove2me | Theorems.Thm_Malliavin_integral_incr_sq
-- name    : Malliavin.integral_incr_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:53:53.241911+00:00
-- url     : https://prove2.me/theorems/2aa1e3b6-f033-4ff8-aa5d-f5e2e2222167
-- title:
--   Malliavin: integral incr sq
-- statement:
--   The variance of a Brownian increment: `E[(B b - B a)²] = b - a`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L710-L725
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L710-L725

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.integral_incr_sq (hB : IsPreBrownianReal B P) {a b : ℝ≥0} (hab : a ≤ b) :
    ∫ ω, (B b ω - B a ω) ^ 2 ∂P = (b : ℝ) - a := by sorry
