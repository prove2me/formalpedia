-- Prove2me | Theorems.Thm_Malliavin_chaosProjection_mem
-- name    : Malliavin.chaosProjection_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:10:58.666319+00:00
-- url     : https://prove2.me/theorems/10c47df9-675a-4581-9bd1-0ab9d49315ed
-- title:
--   Malliavin: chaos Projection mem
-- statement:
--   A selected-range projection takes values in its corresponding closed subspace.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerChaos.lean#L474-L476
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerChaos.lean#L474-L476

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

theorem Malliavin.chaosProjection_mem (hB : IsPreBrownianReal B P) (n : ℕ) (F : RandomL2 P) :
    chaosProjection hB n F ∈ homogeneousChaos hB n := by sorry
