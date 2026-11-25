-- Prove2me | Theorems.Thm_GroundTheory_LocalField_isIrrCharacter_hom
-- name    : GroundTheory.LocalField.isIrrCharacter_hom
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:35:28.512445+00:00
-- url     : https://prove2.me/theorems/b7cb6916-7c8c-4c4f-96ed-f70f66ca94e5
-- title:
--   Local Field: is Irr Character hom
-- statement:
--   The Local Field construction uses the is Irr Character hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionClifford.lean#L49-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionClifford.lean#L49-L51

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionClifford
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

theorem GroundTheory.LocalField.isIrrCharacter_hom (l : G →* ℂˣ) : IsIrrCharacter (fun g ↦ (l g : ℂ)) := by sorry
