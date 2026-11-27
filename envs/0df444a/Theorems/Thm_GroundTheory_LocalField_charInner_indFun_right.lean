-- Prove2me | Theorems.Thm_GroundTheory_LocalField_charInner_indFun_right
-- name    : GroundTheory.LocalField.charInner_indFun_right
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:59:52.312243+00:00
-- url     : https://prove2.me/theorems/eccd05a6-85b1-5fbd-ab40-65d6f5a0f2d8
-- title:
--   Local Field: char Inner ind Fun right
-- statement:
--   The Local Field construction uses the char Inner ind Fun right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionInduced.lean#L104-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionInduced.lean#L104-L106

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

theorem GroundTheory.LocalField.charInner_indFun_right (φ : H →* G) (ψ : H → ℂ) {χ : G → ℂ} (hχ : IsClassFun χ) :
    charInner G χ (indFun φ ψ) = charInner H (χ ∘ φ) ψ := by sorry
