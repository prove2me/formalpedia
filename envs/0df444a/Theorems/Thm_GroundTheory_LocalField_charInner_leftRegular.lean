-- Prove2me | Theorems.Thm_GroundTheory_LocalField_charInner_leftRegular
-- name    : GroundTheory.LocalField.charInner_leftRegular
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:44:03.288531+00:00
-- url     : https://prove2.me/theorems/8cc35a1c-5c5b-4224-a60a-61d9ccc64ff8
-- title:
--   Local Field: char Inner left Regular
-- statement:
--   The Local Field construction uses the char Inner left Regular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionCharacters.lean#L322-L329
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionCharacters.lean#L322-L329

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
variable {G : Type*} [Group G] [Fintype G]

theorem GroundTheory.LocalField.charInner_leftRegular (ψ : G → ℂ) :
    charInner G (Representation.leftRegular ℂ G).character ψ = ψ 1 := by sorry
