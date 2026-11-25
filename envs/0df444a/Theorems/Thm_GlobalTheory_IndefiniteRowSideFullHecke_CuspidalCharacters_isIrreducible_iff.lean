-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CuspidalCharacters_isIrreducible_iff
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.CuspidalCharacters.isIrreducible_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:10:50.273853+00:00
-- url     : https://prove2.me/theorems/6c2f24a4-efd0-4ad7-9aa7-61343c9f859f
-- title:
--   Cuspidal Characters: is Irreducible iff
-- statement:
--   The Cuspidal Characters construction uses the is Irreducible iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/IrreducibleCharacters/CuspidalCharacters.lean#L8-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/IrreducibleCharacters/CuspidalCharacters.lean#L8-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ImportsAlt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_IrreducibleCharacters_CuspidalCharacters
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CuspidalCharacters
open Matrix

theorem GlobalTheory.IndefiniteRowSideFullHecke.CuspidalCharacters.isIrreducible_iff {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) :
    ρ.IsIrreducible ↔ Nontrivial V ∧
      ∀ U : Submodule ℂ V, (∀ g : G, ∀ v ∈ U, ρ g v ∈ U) → U = ⊥ ∨ U = ⊤ := by sorry
