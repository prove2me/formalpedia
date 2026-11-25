-- Prove2me | Theorems.Thm_GroundTheory_LocalField_congrData_of_mem_spanA
-- name    : GroundTheory.LocalField.congrData_of_mem_spanA
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:30:46.69073+00:00
-- url     : https://prove2.me/theorems/1b0a409b-e8e7-4f36-988c-d5cd26b6c7c1
-- title:
--   Local Field: congr Data of mem span A
-- statement:
--   The Local Field construction uses the congr Data of mem span A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionLocal.lean#L241-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionLocal.lean#L241-L249

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

theorem GroundTheory.LocalField.congrData_of_mem_spanA (hζ : IsPrimitiveRoot ζ (Nat.card G)) {b : ℤ} (hab : s ^ a * s ^ b = s)
    (hb : (s ^ b) ^ N = 1) {f : G → ℂ} (hf : f ∈ spanA E ζ) : CongrData ζ N s a f := by sorry
