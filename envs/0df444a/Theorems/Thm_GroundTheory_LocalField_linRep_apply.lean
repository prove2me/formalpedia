-- Prove2me | Theorems.Thm_GroundTheory_LocalField_linRep_apply
-- name    : GroundTheory.LocalField.linRep_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:31:55.874848+00:00
-- url     : https://prove2.me/theorems/75541ad0-c4e7-5762-899c-ba3c13771b66
-- title:
--   Local Field: lin Rep apply
-- statement:
--   The Local Field construction uses the lin Rep apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionClifford.lean#L35-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionClifford.lean#L35-L35

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

theorem GroundTheory.LocalField.linRep_apply (l : G →* ℂˣ) (g : G) (z : ℂ) : linRep l g z = (l g : ℂ) * z := by sorry
