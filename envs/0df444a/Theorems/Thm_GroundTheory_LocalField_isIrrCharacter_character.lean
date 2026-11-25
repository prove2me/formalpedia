-- Prove2me | Theorems.Thm_GroundTheory_LocalField_isIrrCharacter_character
-- name    : GroundTheory.LocalField.isIrrCharacter_character
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:33:27.929241+00:00
-- url     : https://prove2.me/theorems/824a0d86-263a-4d44-ad02-0337d48140b3
-- title:
--   Local Field: is Irr Character character
-- statement:
--   The Local Field construction uses the is Irr Character character property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionCharacters.lean#L125-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionCharacters.lean#L125-L129

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
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
omit [Fintype G]

theorem GroundTheory.LocalField.isIrrCharacter_character (ρ : Representation ℂ G V) [ρ.IsIrreducible] :
    IsIrrCharacter ρ.character := by sorry
