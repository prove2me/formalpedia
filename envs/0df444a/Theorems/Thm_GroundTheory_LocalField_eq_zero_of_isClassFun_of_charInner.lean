-- Prove2me | Theorems.Thm_GroundTheory_LocalField_eq_zero_of_isClassFun_of_charInner
-- name    : GroundTheory.LocalField.eq_zero_of_isClassFun_of_charInner
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:43:54.629019+00:00
-- url     : https://prove2.me/theorems/0720376b-660c-4afe-aa42-2f9d74f35387
-- title:
--   Local Field: eq zero of is Class Fun of char Inner
-- statement:
--   The Local Field construction uses the eq zero of is Class Fun of char Inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionCharacters.lean#L428-L431
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionCharacters.lean#L428-L431

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
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
variable {G : Type*} [Group G] [Fintype G]

theorem GroundTheory.LocalField.eq_zero_of_isClassFun_of_charInner {f : G → ℂ} (hf : IsClassFun f)
    (h : ∀ ψ ∈ irrChars G, charInner G f ψ = 0) : f = 0 := by sorry
