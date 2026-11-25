-- Prove2me | Theorems.Thm_GroundTheory_LocalField_mem_shellSet_iff
-- name    : GroundTheory.LocalField.mem_shellSet_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:31:11.742999+00:00
-- url     : https://prove2.me/theorems/0c1a4e6b-3ba4-4975-ab9d-b580ad6c31ea
-- title:
--   Local Field: mem shell Set iff
-- statement:
--   The Local Field construction uses the mem shell Set iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZeta.lean#L55-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZeta.lean#L55-L58

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaGauss
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
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
open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem GroundTheory.LocalField.mem_shellSet_iff {x : K} (hx : x ≠ 0) {j : ℤ} :
    x ∈ (valBall K j : Set K) \ valBall K (j + 1) ↔ ord x = j := by sorry
