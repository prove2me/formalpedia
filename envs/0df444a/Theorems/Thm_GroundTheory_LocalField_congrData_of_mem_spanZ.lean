-- Prove2me | Theorems.Thm_GroundTheory_LocalField_congrData_of_mem_spanZ
-- name    : GroundTheory.LocalField.congrData_of_mem_spanZ
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:31:30.233484+00:00
-- url     : https://prove2.me/theorems/11c4dc40-aff9-4a41-ab40-5fbcc5db74b7
-- title:
--   Local Field: congr Data of mem span Z
-- statement:
--   The Local Field construction uses the congr Data of mem span Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionLocal.lean#L231-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionLocal.lean#L231-L239

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionSpan
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionLocal
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
open Module Representation
open scoped Classical
universe u
variable {G : Type u} [Group G] [Fintype G]
variable {ζ : ℂ} {N : ℕ} {s : G} {a : ℤ}
variable {E : Subgroup G → Prop}

theorem GroundTheory.LocalField.congrData_of_mem_spanZ (hζ : IsPrimitiveRoot ζ (Nat.card G)) {b : ℤ} (hab : s ^ a * s ^ b = s)
    (hb : (s ^ b) ^ N = 1) {f : G → ℂ} (hf : f ∈ spanZ E) : CongrData ζ N s a f := by sorry
