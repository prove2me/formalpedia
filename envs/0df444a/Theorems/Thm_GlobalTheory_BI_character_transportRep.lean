-- Prove2me | Theorems.Thm_GlobalTheory_BI_character_transportRep
-- name    : GlobalTheory.BI.character_transportRep
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:57:54.69434+00:00
-- url     : https://prove2.me/theorems/f412e20f-adf7-48ce-a1cf-deffd2294dc4
-- title:
--   BI: character transport Rep
-- statement:
--   The BI construction uses the character transport Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterOverSubfieldOfRepresentation.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterOverSubfieldOfRepresentation.lean#L18-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldOfRepresentation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI
noncomputable section
open GlobalTheory GlobalTheory.BI
variable {K G V W : Type} [Field K] [Group G] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

theorem GlobalTheory.BI.character_transportRep [FiniteDimensional K V] [FiniteDimensional K W]
    (ρ : Representation K G V) (e : V ≃ₗ[K] W) (g : G) :
    (transportRep ρ e).character g = ρ.character g := by sorry
