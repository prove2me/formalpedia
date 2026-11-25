-- Prove2me | Theorems.Thm_GroundTheory_LocalField_character_linRep
-- name    : GroundTheory.LocalField.character_linRep
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:45:49.097427+00:00
-- url     : https://prove2.me/theorems/9df15d53-2225-4ef0-b10a-e4ec7dce0d8a
-- title:
--   Local Field: character lin Rep
-- statement:
--   The Local Field construction uses the character lin Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionClifford.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionClifford.lean#L37-L39

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

theorem GroundTheory.LocalField.character_linRep (l : G →* ℂˣ) : (linRep l).character = fun g ↦ (l g : ℂ) := by sorry
