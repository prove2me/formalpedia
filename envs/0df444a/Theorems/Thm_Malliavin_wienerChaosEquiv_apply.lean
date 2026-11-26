-- Prove2me | Theorems.Thm_Malliavin_wienerChaosEquiv_apply
-- name    : Malliavin.wienerChaosEquiv_apply
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:10:06.862327+00:00
-- url     : https://prove2.me/theorems/9d27b2da-8743-4eb9-ab72-e27f4b074505
-- title:
--   Malliavin: wiener Chaos Equiv apply
-- statement:
--   The coordinate determined by totality is the corresponding selected-subspace projection.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerChaos.lean#L519-L524
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerChaos.lean#L519-L524

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

theorem Malliavin.wienerChaosEquiv_apply (hB : IsPreBrownianReal B P) (htotal : IsWienerTotal hB)
    (F : RandomL2 P) (n : ℕ) :
    (wienerChaosEquiv hB htotal F) n =
      (homogeneousChaos hB n : Submodule ℝ (RandomL2 P)).orthogonalProjectionOnto F := by sorry
