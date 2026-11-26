-- Prove2me | Theorems.Thm_Malliavin_brownianLp_half_notMem_closure_span_unitIncrementLp
-- name    : Malliavin.brownianLp_half_notMem_closure_span_unitIncrementLp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:54:00.248479+00:00
-- url     : https://prove2.me/theorems/8225ff24-7bd0-5378-9617-6e505b9aca4b
-- title:
--   Malliavin: brownian Lp half not Mem closure span unit Increment Lp
-- statement:
--   `B (1/2)` does not lie in the closed span of the unit increments: its inner product with
--   `B 1 - B 0` is `1/2` and with all other unit increments `0`, while `‖B (1/2)‖² = 1/2 ≠ 1/4`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L995-L1063
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L995-L1063

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.brownianLp_half_notMem_closure_span_unitIncrementLp (hB : IsPreBrownianReal B P) :
    brownianLp hB (1 / 2) ∉
      (Submodule.span ℝ (Set.range (unitIncrementLp hB))).topologicalClosure := by sorry
