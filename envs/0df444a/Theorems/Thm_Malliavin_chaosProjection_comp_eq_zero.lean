-- Prove2me | Theorems.Thm_Malliavin_chaosProjection_comp_eq_zero
-- name    : Malliavin.chaosProjection_comp_eq_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:09:46.668798+00:00
-- url     : https://prove2.me/theorems/4a457092-7060-52f8-8049-ef03bee866de
-- title:
--   Malliavin: chaos Projection comp eq zero
-- statement:
--   Projections onto distinct selected homogeneous subspaces compose to zero.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerChaos.lean#L479-L486
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerChaos.lean#L479-L486

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

theorem Malliavin.chaosProjection_comp_eq_zero (hB : IsPreBrownianReal B P) {m n : ℕ}
    (hmn : m ≠ n) :
    chaosProjection hB m ∘L chaosProjection hB n = 0 := by sorry
