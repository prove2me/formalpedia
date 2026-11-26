-- Prove2me | Theorems.Thm_Malliavin_multipleIntegralCLM_mem_homogeneousChaos
-- name    : Malliavin.multipleIntegralCLM_mem_homogeneousChaos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:08:56.053979+00:00
-- url     : https://prove2.me/theorems/c4d542fa-dfb3-5ab4-9ae1-e8f53529d243
-- title:
--   Malliavin: multiple Integral CLM mem homogeneous Chaos
-- statement:
--   Every output of the selected order-`n` multiple operator belongs to its closed range.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerChaos.lean#L63-L67
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerChaos.lean#L63-L67

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

theorem Malliavin.multipleIntegralCLM_mem_homogeneousChaos (hB : IsPreBrownianReal B P) (n : ℕ)
    (f : IteratedKernel n) :
    multipleIntegralCLM hB n f ∈ homogeneousChaos hB n := by sorry
