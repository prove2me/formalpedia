-- Prove2me | Theorems.Thm_GroundTheory_LocalField_character_leftRegular_eq_sum
-- name    : GroundTheory.LocalField.character_leftRegular_eq_sum
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:43:41.622615+00:00
-- url     : https://prove2.me/theorems/eaf9e1f1-7516-4f7d-befe-3bbebaddf7d8
-- title:
--   Local Field: character left Regular eq sum
-- statement:
--   The Local Field construction uses the character left Regular eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionCharacters.lean#L331-L334
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionCharacters.lean#L331-L334

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

theorem GroundTheory.LocalField.character_leftRegular_eq_sum :
    (Representation.leftRegular ℂ G).character = ∑ ψ ∈ irrChars G, ψ 1 • ψ := by sorry
