-- Prove2me | Theorems.Thm_GroundTheory_LocalField_IsIrrCharacter_isCharacter
-- name    : GroundTheory.LocalField.IsIrrCharacter.isCharacter
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:24:24.004511+00:00
-- url     : https://prove2.me/theorems/37beec90-536e-457b-a288-13be0c9b33b1
-- title:
--   Is Irr Character: is Character
-- statement:
--   The Is Irr Character construction uses the is Character property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionCharacters.lean#L141-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionCharacters.lean#L141-L143

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

theorem GroundTheory.LocalField.IsIrrCharacter.isCharacter {χ : G → ℂ} (h : IsIrrCharacter χ) : IsCharacter χ := by sorry
