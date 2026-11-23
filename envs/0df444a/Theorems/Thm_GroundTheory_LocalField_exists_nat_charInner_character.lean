-- Prove2me | Theorems.Thm_GroundTheory_LocalField_exists_nat_charInner_character
-- name    : GroundTheory.LocalField.exists_nat_charInner_character
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:14.036522+00:00
-- url     : https://prove2.me/theorems/86927b7b-f9bd-422d-b7ae-070986d9aacc
-- title:
--   Local Field: exists nat char Inner character
-- statement:
--   The Local Field construction uses the exists nat char Inner character property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionCharacters.lean#L281-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionCharacters.lean#L281-L285

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
universe u
variable {G : Type*} [Group G] [Fintype G]

theorem GroundTheory.LocalField.exists_nat_charInner_character {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) {ψ : G → ℂ} (hψ : IsIrrCharacter ψ) :
    ∃ m : ℕ, charInner G ρ.character ψ = m := by sorry
