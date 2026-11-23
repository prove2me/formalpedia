-- Prove2me | Theorems.Thm_GroundTheory_LocalField_charInner_character_character
-- name    : GroundTheory.LocalField.charInner_character_character
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:24:31.679996+00:00
-- url     : https://prove2.me/theorems/e766e068-7299-4bb5-bc2b-9cc226ca502f
-- title:
--   Local Field: char Inner character character
-- statement:
--   The Local Field construction uses the char Inner character character property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionCharacters.lean#L131-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionCharacters.lean#L131-L136

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

theorem GroundTheory.LocalField.charInner_character_character {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    charInner G σ.character ρ.character = finrank ℂ (IntertwiningMap ρ σ) := by sorry
