-- Prove2me | Theorems.Thm_GroundTheory_LocalField_indFun_indFun
-- name    : GroundTheory.LocalField.indFun_indFun
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:37:15.652338+00:00
-- url     : https://prove2.me/theorems/9b283612-73eb-4ff6-9acf-80602a0345ac
-- title:
--   Local Field: ind Fun ind Fun
-- statement:
--   The Local Field construction uses the ind Fun ind Fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionInduced.lean#L115-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionInduced.lean#L115-L121

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced
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
variable {G H K : Type*} [Group G] [Group H] [Group K] [Fintype G] [Fintype H] [Fintype K]

theorem GroundTheory.LocalField.indFun_indFun (φ : H →* G) (φ' : K →* H) (ψ : K → ℂ) :
    indFun φ (indFun φ' ψ) = indFun (φ.comp φ') ψ := by sorry
