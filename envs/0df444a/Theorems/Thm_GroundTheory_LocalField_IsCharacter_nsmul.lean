-- Prove2me | Theorems.Thm_GroundTheory_LocalField_IsCharacter_nsmul
-- name    : GroundTheory.LocalField.IsCharacter.nsmul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:44:09.135805+00:00
-- url     : https://prove2.me/theorems/2f3ef423-f0a7-4232-8ab9-be35a20495d6
-- title:
--   Is Character: nsmul
-- statement:
--   The Is Character construction uses the nsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionCharacters.lean#L470-L473
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionCharacters.lean#L470-L473

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
variable {G : Type*} [Group G]

theorem GroundTheory.LocalField.IsCharacter.nsmul {χ : G → ℂ} (hχ : IsCharacter χ) (n : ℕ) : IsCharacter (n • χ) := by sorry
