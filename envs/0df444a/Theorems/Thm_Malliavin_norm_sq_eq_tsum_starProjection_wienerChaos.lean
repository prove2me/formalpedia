-- Prove2me | Theorems.Thm_Malliavin_norm_sq_eq_tsum_starProjection_wienerChaos
-- name    : Malliavin.norm_sq_eq_tsum_starProjection_wienerChaos
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:10:39.514796+00:00
-- url     : https://prove2.me/theorems/b573d930-d908-4556-b019-a878a2260936
-- title:
--   Malliavin: norm sq eq tsum star Projection wiener Chaos
-- statement:
--   Parseval identity for the selected-tower expansion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerChaos.lean#L543-L562
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerChaos.lean#L543-L562

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

theorem Malliavin.norm_sq_eq_tsum_starProjection_wienerChaos
    (hB : IsPreBrownianReal B P)
    (hsum : IsHilbertSum ℝ
      (fun n : ℕ => ↥(homogeneousChaos hB n : Submodule ℝ (RandomL2 P)))
      (fun n : ℕ => (homogeneousChaos hB n : Submodule ℝ (RandomL2 P)).subtypeₗᵢ))
    (F : RandomL2 P) :
    ‖F‖ ^ 2 = ∑' n : ℕ,
      ‖(homogeneousChaos hB n : Submodule ℝ (RandomL2 P)).starProjection F‖ ^ 2 := by sorry
