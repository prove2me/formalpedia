-- Prove2me | Theorems.Thm_GroundTheory_LocalField_mem_irrChars
-- name    : GroundTheory.LocalField.mem_irrChars
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:24:25.423822+00:00
-- url     : https://prove2.me/theorems/f8d60e83-c41d-44df-b5bf-37c8e5cca632
-- title:
--   Local Field: mem irr Chars
-- statement:
--   The Local Field construction uses the mem irr Chars property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionCharacters.lean#L202-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionCharacters.lean#L202-L203

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

theorem GroundTheory.LocalField.mem_irrChars {χ : G → ℂ} : χ ∈ irrChars G ↔ IsIrrCharacter χ := by sorry
