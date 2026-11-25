-- Prove2me | Theorems.Thm_GroundTheory_LocalField_IsIrrCharacter_exists_eq_indFun_of_isNilpotent
-- name    : GroundTheory.LocalField.IsIrrCharacter.exists_eq_indFun_of_isNilpotent
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:35:08.476267+00:00
-- url     : https://prove2.me/theorems/9aab2b8f-c21c-413a-bf0a-a98269d71ae6
-- title:
--   Is Irr Character: exists eq ind Fun of is Nilpotent
-- statement:
--   The Is Irr Character construction uses the exists eq ind Fun of is Nilpotent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionMonomial.lean#L223-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionMonomial.lean#L223-L226

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionClifford
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionMonomial
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
open Classical

theorem GroundTheory.LocalField.IsIrrCharacter.exists_eq_indFun_of_isNilpotent {G : Type*} [Group G] [Fintype G]
    [Group.IsNilpotent G] {χ : G → ℂ} (h : IsIrrCharacter χ) :
    ∃ (K : Subgroup G) (l : K →* ℂˣ), χ = indFun K.subtype (fun k ↦ (l k : ℂ)) := by sorry
