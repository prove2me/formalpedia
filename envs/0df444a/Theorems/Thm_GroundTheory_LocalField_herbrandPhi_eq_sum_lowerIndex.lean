-- Prove2me | Theorems.Thm_GroundTheory_LocalField_herbrandPhi_eq_sum_lowerIndex
-- name    : GroundTheory.LocalField.herbrandPhi_eq_sum_lowerIndex
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:46:20.928713+00:00
-- url     : https://prove2.me/theorems/eff39094-f9fe-4c7e-983f-d87f55cafd0f
-- title:
--   Local Field: herbrand Phi eq sum lower Index
-- statement:
--   The Local Field construction uses the herbrand Phi eq sum lower Index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HerbrandFunction.lean#L223-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HerbrandFunction.lean#L223-L246

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LowerIndex
import Definitions.Def_GroundTheory_LocalFields_HerbrandFunction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel Filter Topology MeasureTheory
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable {K L}

theorem GroundTheory.LocalField.herbrandPhi_eq_sum_lowerIndex {u : ℝ} (hu : -1 ≤ u) :
    herbrandPhi K L u = (Nat.card (lowerRamificationGroup K L 0) : ℝ)⁻¹ *
      ∑ σ : L ≃ₐ[K] L, enatMin (lowerIndex K L σ) (u + 1) - 1 := by sorry
