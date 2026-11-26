-- Prove2me | Theorems.Thm_Malliavin_isWienerTotal_of_generated
-- name    : Malliavin.isWienerTotal_of_generated
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:08:59.872838+00:00
-- url     : https://prove2.me/theorems/2bf0bee9-50ee-4061-8704-df9dfc0dcaed
-- title:
--   Malliavin: is Wiener Total of generated
-- statement:
--   Density of finite sums of the selected homogeneous ranges on a Brownian-generated space.
--
--   Sigma-generation supplies second-countability and makes process-measurable `L²` exhaust the
--   ambient space, so `isWienerTotal_of_processLpEmbedding` applies.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerChaos.lean#L434-L440
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerChaos.lean#L434-L440

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

theorem Malliavin.isWienerTotal_of_generated (hB : IsPreBrownianReal B P)
    (hgen : IsWienerGenerated B) : IsWienerTotal hB := by sorry
