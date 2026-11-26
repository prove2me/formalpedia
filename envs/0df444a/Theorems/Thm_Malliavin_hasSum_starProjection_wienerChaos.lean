-- Prove2me | Theorems.Thm_Malliavin_hasSum_starProjection_wienerChaos
-- name    : Malliavin.hasSum_starProjection_wienerChaos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:10:00.606808+00:00
-- url     : https://prove2.me/theorems/e2b3e322-5be1-5a32-bf44-0458945c93da
-- title:
--   Malliavin: has Sum star Projection wiener Chaos
-- statement:
--   Selected-tower expansion as the sum of ambient orthogonal projections.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerChaos.lean#L527-L540
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerChaos.lean#L527-L540

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

theorem Malliavin.hasSum_starProjection_wienerChaos
    (hB : IsPreBrownianReal B P)
    (hsum : IsHilbertSum ℝ
      (fun n : ℕ => ↥(homogeneousChaos hB n : Submodule ℝ (RandomL2 P)))
      (fun n : ℕ => (homogeneousChaos hB n : Submodule ℝ (RandomL2 P)).subtypeₗᵢ))
    (F : RandomL2 P) :
    HasSum (fun n : ℕ =>
      (homogeneousChaos hB n : Submodule ℝ (RandomL2 P)).starProjection F) F := by sorry
