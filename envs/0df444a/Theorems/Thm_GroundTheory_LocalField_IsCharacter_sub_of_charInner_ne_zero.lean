-- Prove2me | Theorems.Thm_GroundTheory_LocalField_IsCharacter_sub_of_charInner_ne_zero
-- name    : GroundTheory.LocalField.IsCharacter.sub_of_charInner_ne_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:35:17.84884+00:00
-- url     : https://prove2.me/theorems/d2b6c4e9-0abf-4d77-8843-d7c42dca19a9
-- title:
--   Is Character: sub of char Inner ne zero
-- statement:
--   The Is Character construction uses the sub of char Inner ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionClifford.lean#L105-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionClifford.lean#L105-L118

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
variable [Fintype G]

theorem GroundTheory.LocalField.IsCharacter.sub_of_charInner_ne_zero {η χ : G → ℂ} (hη : IsCharacter η)
    (hχ : IsIrrCharacter χ) (h : charInner G η χ ≠ 0) : IsCharacter (η - χ) := by sorry
