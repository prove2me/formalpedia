-- Prove2me | Theorems.Thm_GroundTheory_LocalField_modulus_le_of_mem_valBall
-- name    : GroundTheory.LocalField.modulus_le_of_mem_valBall
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:32:18.221047+00:00
-- url     : https://prove2.me/theorems/ce2b91c7-93e7-41da-8315-8e963fba2d53
-- title:
--   Local Field: modulus le of mem val Ball
-- statement:
--   The Local Field construction uses the modulus le of mem val Ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierHaar.lean#L195-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierHaar.lean#L195-L201

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_SeparableClosureValuation
import Definitions.Def_GroundTheory_LocalFields_LocalFourierHaar
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
open ValuativeRel MeasureTheory Measure Topology Filter TopologicalSpace
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem GroundTheory.LocalField.modulus_le_of_mem_valBall {n : ℤ} {x : K} (hx : x ∈ valBall K n) :
    modulus x ≤ (residueCard K : ℝ≥0) ^ (-n) := by sorry
