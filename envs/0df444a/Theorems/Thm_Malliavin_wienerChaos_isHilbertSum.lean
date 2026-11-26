-- Prove2me | Theorems.Thm_Malliavin_wienerChaos_isHilbertSum
-- name    : Malliavin.wienerChaos_isHilbertSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:09:35.7157+00:00
-- url     : https://prove2.me/theorems/58d38084-402a-4340-86c1-9e0b22f1fd70
-- title:
--   Malliavin: wiener Chaos is Hilbert Sum
-- statement:
--   Hilbert-sum decomposition of the selected homogeneous ranges on a generated space.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerChaos.lean#L461-L466
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerChaos.lean#L461-L466

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

theorem Malliavin.wienerChaos_isHilbertSum (hB : IsPreBrownianReal B P)
    (hgen : IsWienerGenerated B) :
    IsHilbertSum ℝ
      (fun n : ℕ => ↥(homogeneousChaos hB n : Submodule ℝ (RandomL2 P)))
      (fun n : ℕ => (homogeneousChaos hB n : Submodule ℝ (RandomL2 P)).subtypeₗᵢ) := by sorry
