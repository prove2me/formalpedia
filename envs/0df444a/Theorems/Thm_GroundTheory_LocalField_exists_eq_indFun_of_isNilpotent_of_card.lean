-- Prove2me | Theorems.Thm_GroundTheory_LocalField_exists_eq_indFun_of_isNilpotent_of_card
-- name    : GroundTheory.LocalField.exists_eq_indFun_of_isNilpotent_of_card
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:31:36.071848+00:00
-- url     : https://prove2.me/theorems/272cebec-fe80-4106-8307-7f840e787ae1
-- title:
--   Local Field: exists eq ind Fun of is Nilpotent of card
-- statement:
--   The Local Field construction uses the exists eq ind Fun of is Nilpotent of card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionMonomial.lean#L153-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionMonomial.lean#L153-L219

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionClifford
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionMonomial
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
universe u
open Classical

theorem GroundTheory.LocalField.exists_eq_indFun_of_isNilpotent_of_card (n : ℕ) :
    ∀ (G : Type u) [Group G] [Fintype G] [Group.IsNilpotent G], Nat.card G = n →
      ∀ {χ : G → ℂ}, IsIrrCharacter χ →
        ∃ (K : Subgroup G) (l : K →* ℂˣ), χ = indFun K.subtype (fun k ↦ (l k : ℂ)) := by sorry
