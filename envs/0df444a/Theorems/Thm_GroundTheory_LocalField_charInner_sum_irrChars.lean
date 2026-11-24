-- Prove2me | Theorems.Thm_GroundTheory_LocalField_charInner_sum_irrChars
-- name    : GroundTheory.LocalField.charInner_sum_irrChars
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:43:59.704722+00:00
-- url     : https://prove2.me/theorems/bf711ccf-7fbe-44a4-bc3e-03e23dfe9082
-- title:
--   Local Field: char Inner sum irr Chars
-- statement:
--   The Local Field construction uses the char Inner sum irr Chars property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionCharacters.lean#L205-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionCharacters.lean#L205-L215

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
universe u
variable {G : Type*} [Group G] [Fintype G]

theorem GroundTheory.LocalField.charInner_sum_irrChars (c : (G → ℂ) → ℂ) {ψ : G → ℂ} (hψ : ψ ∈ irrChars G) :
    charInner G (∑ χ ∈ irrChars G, c χ • χ) ψ = c ψ := by sorry
