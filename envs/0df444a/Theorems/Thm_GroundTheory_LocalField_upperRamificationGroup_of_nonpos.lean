-- Prove2me | Theorems.Thm_GroundTheory_LocalField_upperRamificationGroup_of_nonpos
-- name    : GroundTheory.LocalField.upperRamificationGroup_of_nonpos
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:47:43.477155+00:00
-- url     : https://prove2.me/theorems/7c23fbe6-aed9-53f7-b379-9a84842b7cd4
-- title:
--   Local Field: upper Ramification Group of nonpos
-- statement:
--   The Local Field construction uses the upper Ramification Group of nonpos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HerbrandFunction.lean#L417-L419
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HerbrandFunction.lean#L417-L419

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

theorem GroundTheory.LocalField.upperRamificationGroup_of_nonpos {v : ℝ} (hv : v ≤ 0) :
    upperRamificationGroup K L v = lowerRamificationGroupReal K L v := by sorry
