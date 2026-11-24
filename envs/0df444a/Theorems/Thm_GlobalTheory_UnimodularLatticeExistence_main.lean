-- Prove2me | Theorems.Thm_GlobalTheory_UnimodularLatticeExistence_main
-- name    : GlobalTheory.UnimodularLatticeExistence.main
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:50:29.86626+00:00
-- url     : https://prove2.me/theorems/f284aa92-9c48-47c9-9cd4-829cc4079c72
-- title:
--   Unimodular Lattice Existence: main
-- statement:
--   The Unimodular Lattice Existence construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ImportsAlt.lean#L9-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ImportsAlt.lean#L9-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ImportsAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.UnimodularLatticeExistence
open Representation

theorem GlobalTheory.UnimodularLatticeExistence.main : ∀ {G : Type u_1} [inst : Group G] {V : Type u_2} [inst_1 : AddCommGroup V] [inst_2 : Module ℂ V] (ρ : Representation ℂ G V), Representation.IsIrreducible ρ ↔ Nontrivial V ∧ ∀ (U : Submodule ℂ V), (∀ (g : G), ∀ v ∈ U, ((ρ : G → V →ₗ[ℂ] V) g : V → V) v ∈ U) → U = ⊥ ∨ U = ⊤ := by sorry
