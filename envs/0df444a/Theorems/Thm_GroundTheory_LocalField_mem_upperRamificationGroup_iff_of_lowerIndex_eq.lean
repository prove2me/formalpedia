-- Prove2me | Theorems.Thm_GroundTheory_LocalField_mem_upperRamificationGroup_iff_of_lowerIndex_eq
-- name    : GroundTheory.LocalField.mem_upperRamificationGroup_iff_of_lowerIndex_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:43:26.186839+00:00
-- url     : https://prove2.me/theorems/f4d57d6a-80e4-48a0-a7b6-87ce9561dc8e
-- title:
--   Local Field: mem upper Ramification Group iff of lower Index eq
-- statement:
--   The Local Field construction uses the mem upper Ramification Group iff of lower Index eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HerbrandFunction.lean#L432-L437
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HerbrandFunction.lean#L432-L437

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

theorem GroundTheory.LocalField.mem_upperRamificationGroup_iff_of_lowerIndex_eq {v : ℝ} {σ : L ≃ₐ[K] L} {m : ℕ}
    (h : lowerIndex K L σ = m) :
    σ ∈ upperRamificationGroup K L v ↔ v ≤ herbrandPhi K L ((m : ℝ) - 1) := by sorry
