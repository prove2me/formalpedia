-- Prove2me | Theorems.Thm_GroundTheory_LocalField_isCharacter_iff
-- name    : GroundTheory.LocalField.isCharacter_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:34.191301+00:00
-- url     : https://prove2.me/theorems/6622565a-22ca-4d29-8cb4-f78bee00ae74
-- title:
--   Local Field: is Character iff
-- statement:
--   The Local Field construction uses the is Character iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionCharacters.lean#L486-L499
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionCharacters.lean#L486-L499

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
variable [Fintype G]

theorem GroundTheory.LocalField.isCharacter_iff {f : G → ℂ} :
    IsCharacter f ↔ IsClassFun f ∧ ∀ ψ ∈ irrChars G, ∃ n : ℕ, charInner G f ψ = n := by sorry
