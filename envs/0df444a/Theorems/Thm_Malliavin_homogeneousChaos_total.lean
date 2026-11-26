-- Prove2me | Theorems.Thm_Malliavin_homogeneousChaos_total
-- name    : Malliavin.homogeneousChaos_total
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:10:07.927258+00:00
-- url     : https://prove2.me/theorems/16f9f9b5-d660-4cbb-941c-bee8798294af
-- title:
--   Malliavin: homogeneous Chaos total
-- statement:
--   Expanded form of `isWienerTotal_of_generated`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerChaos.lean#L443-L446
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerChaos.lean#L443-L446

import Definitions.Def_Malliavin_MultipleIntegral
import Definitions.Def_Malliavin_WienerChaos
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Topology symmDiff
noncomputable section
open Malliavin
universe u v u_1 u_2 u_4 u_6
universe u₁ u₂ u₃
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.homogeneousChaos_total (hB : IsPreBrownianReal B P)
    (hgen : IsWienerGenerated B) :
    (⨆ n : ℕ, (homogeneousChaos hB n : Submodule ℝ (RandomL2 P))).topologicalClosure = ⊤ := by sorry
