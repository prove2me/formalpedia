-- Prove2me | Theorems.Thm_Malliavin_dense_span_boxKernel_one
-- name    : Malliavin.dense_span_boxKernel_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:52:47.34089+00:00
-- url     : https://prove2.me/theorems/b18470e2-423f-4c1f-a4e1-b6f28c2eda8b
-- title:
--   Malliavin: dense span box Kernel one
-- statement:
--   The box indicators `1_{(0, t]}` have dense span among order-one kernels.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L534-L557
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L534-L557

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.dense_span_boxKernel_one :
    Dense (Submodule.span ℝ
      (Set.range fun t : ℝ≥0 ↦ boxKernel (fun _ : Fin 1 ↦ 0) (fun _ ↦ t)) :
        Set (IteratedKernel 1)) := by sorry
