-- Prove2me | Theorems.Thm_GroundTheory_LocalField_mem_range_unitsIncl_iff
-- name    : GroundTheory.LocalField.mem_range_unitsIncl_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:16:41.890705+00:00
-- url     : https://prove2.me/theorems/1a722739-1fe6-4ba4-9061-54d7a219e359
-- title:
--   Local Field: mem range units Incl iff
-- statement:
--   The Local Field construction uses the mem range units Incl iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnitsBasic.lean#L178-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnitsBasic.lean#L178-L191

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing
open scoped WithZero
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {K}

theorem GroundTheory.LocalField.mem_range_unitsIncl_iff {x : Kˣ} :
    x ∈ (unitsIncl K).range ↔ normalizedValuation K x = 1 := by sorry
