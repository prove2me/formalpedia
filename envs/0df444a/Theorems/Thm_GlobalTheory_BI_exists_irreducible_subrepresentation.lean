-- Prove2me | Theorems.Thm_GlobalTheory_BI_exists_irreducible_subrepresentation
-- name    : GlobalTheory.BI.exists_irreducible_subrepresentation
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:57:57.161986+00:00
-- url     : https://prove2.me/theorems/8eb3ed66-6f37-49a3-a384-4d6a4301edaa
-- title:
--   BI: exists irreducible subrepresentation
-- statement:
--   The BI construction uses the exists irreducible subrepresentation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsIrrCharAdd.lean#L8-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsIrrCharAdd.lean#L8-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldOfRepresentationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsCharacterQuotientOfInjectiveIntertwiningStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsIrrCharAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI
open GlobalTheory GlobalTheory.BI

theorem GlobalTheory.BI.exists_irreducible_subrepresentation {K G V : Type} [Field K] [Group G] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Nontrivial V] (ρ : Representation K G V) :
    ∃ S : Subrepresentation ρ, S.toRepresentation.IsIrreducible := by sorry
