-- Prove2me | Theorems.Thm_Malliavin_integral_eq_inner_const
-- name    : Malliavin.integral_eq_inner_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:52:20.792376+00:00
-- url     : https://prove2.me/theorems/ed588ac8-cfa1-53c5-a9bc-62ed14cf06aa
-- title:
--   Malliavin: integral eq inner const
-- statement:
--   Expectation on `L²(P)` is the pairing with the constant `1`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L326-L333
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L326-L333

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
omit [MeasurableSpace Ω]

theorem Malliavin.integral_eq_inner_const {m : MeasurableSpace Ω} (P : Measure Ω) [IsFiniteMeasure P]
    (X : Lp ℝ 2 P) :
    ∫ ω, X ω ∂P = ⟪X, Lp.const 2 P (1 : ℝ)⟫_ℝ := by sorry
