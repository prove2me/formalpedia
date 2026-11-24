-- Prove2me | Theorems.Thm_GroundTheory_LocalField_IsElementaryAt_isNilpotent
-- name    : GroundTheory.LocalField.IsElementaryAt.isNilpotent
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:43:50.760361+00:00
-- url     : https://prove2.me/theorems/67250ad2-42d0-47af-a6d1-426761eac569
-- title:
--   Is Elementary At: is Nilpotent
-- statement:
--   The Is Elementary At construction uses the is Nilpotent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionElementary.lean#L94-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionElementary.lean#L94-L139

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionElementary
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
variable {G : Type*} [Group G]
variable [Finite G] {p : ℕ}

theorem GroundTheory.LocalField.IsElementaryAt.isNilpotent (hp : p.Prime) {H : Subgroup G} (hH : IsElementaryAt p H) :
    Group.IsNilpotent H := by sorry
