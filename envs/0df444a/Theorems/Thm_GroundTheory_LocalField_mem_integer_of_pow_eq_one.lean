-- Prove2me | Theorems.Thm_GroundTheory_LocalField_mem_integer_of_pow_eq_one
-- name    : GroundTheory.LocalField.mem_integer_of_pow_eq_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:32:45.495506+00:00
-- url     : https://prove2.me/theorems/7e44dbcf-a8ec-4982-9e90-62d499ba85cb
-- title:
--   Local Field: mem integer of pow eq one
-- statement:
--   The Local Field construction uses the mem integer of pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedRootsOfUnity.lean#L60-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedRootsOfUnity.lean#L60-L66

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
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
open ValuativeRel Polynomial
variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
omit [TopologicalSpace L] [IsNonarchimedeanLocalField L]

theorem GroundTheory.LocalField.mem_integer_of_pow_eq_one {m : ℕ} (hm : m ≠ 0) {x : L} (hx : x ^ m = 1) : x ∈ 𝒪[L] := by sorry
