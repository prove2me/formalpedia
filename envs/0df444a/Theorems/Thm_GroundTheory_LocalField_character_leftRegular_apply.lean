-- Prove2me | Theorems.Thm_GroundTheory_LocalField_character_leftRegular_apply
-- name    : GroundTheory.LocalField.character_leftRegular_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:13.102801+00:00
-- url     : https://prove2.me/theorems/da2a65b8-4493-4bcd-9850-e2cf1f1670cd
-- title:
--   Local Field: character left Regular apply
-- statement:
--   The Local Field construction uses the character left Regular apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionCharacters.lean#L304-L320
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionCharacters.lean#L304-L320

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

theorem GroundTheory.LocalField.character_leftRegular_apply [DecidableEq G] (g : G) :
    (Representation.leftRegular ℂ G).character g = if g = 1 then (Fintype.card G : ℂ) else 0 := by sorry
