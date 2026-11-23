-- Prove2me | Theorems.Thm_GroundTheory_LocalField_algebraMap_mem_integer_iff
-- name    : GroundTheory.LocalField.algebraMap_mem_integer_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:18:04.594823+00:00
-- url     : https://prove2.me/theorems/1d57e111-00b3-4e8f-9778-379d017235e0
-- title:
--   Local Field: algebra Map mem integer iff
-- statement:
--   The Local Field construction uses the algebra Map mem integer iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Interface.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Interface.lean#L27-L29

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
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
open ValuativeRel
variable (K L : Type*) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Algebra K L] [ValuativeExtension K L]

theorem GroundTheory.LocalField.algebraMap_mem_integer_iff (x : K) : algebraMap K L x ∈ 𝒪[L] ↔ x ∈ 𝒪[K] := by sorry
