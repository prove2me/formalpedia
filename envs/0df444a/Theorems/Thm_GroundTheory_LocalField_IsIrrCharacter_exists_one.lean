-- Prove2me | Theorems.Thm_GroundTheory_LocalField_IsIrrCharacter_exists_one
-- name    : GroundTheory.LocalField.IsIrrCharacter.exists_one
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:43:40.490665+00:00
-- url     : https://prove2.me/theorems/62384fcf-7ab4-4ce1-8526-1a400f9778c5
-- title:
--   Is Irr Character: exists one
-- statement:
--   The Is Irr Character construction uses the exists one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionCharacters.lean#L166-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionCharacters.lean#L166-L174

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
omit [Fintype G]

theorem GroundTheory.LocalField.IsIrrCharacter.exists_one {χ : G → ℂ} (h : IsIrrCharacter χ) : ∃ n : ℕ, 0 < n ∧ χ 1 = n := by sorry
