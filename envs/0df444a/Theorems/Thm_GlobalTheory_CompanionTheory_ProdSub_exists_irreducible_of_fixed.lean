-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ProdSub_exists_irreducible_of_fixed
-- name    : GlobalTheory.CompanionTheory.ProdSub.exists_irreducible_of_fixed
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:56:38.484251+00:00
-- url     : https://prove2.me/theorems/7eb433fd-d636-46b8-b256-968b9709ebf8
-- title:
--   Prod Sub: exists irreducible of fixed
-- statement:
--   The Prod Sub construction uses the exists irreducible of fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsIrreducibleOfFixed.lean#L57-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsIrreducibleOfFixed.lean#L57-L153

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsIrreducibleOfFixed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ProdSub
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem GlobalTheory.CompanionTheory.ProdSub.exists_irreducible_of_fixed {π : Representation ℂ G V} {K : Subgroup G} {W : Submodule ℂ V}
    (hW : ∀ g, ∀ ⦃x⦄, x ∈ W → π g x ∈ W) (hW0 : W ≠ ⊥)
    (hfin : FiniteDimensional ℂ ↥(W ⊓ fixed π K))
    (hnz : ∀ A : Submodule ℂ V, (∀ g, ∀ ⦃x⦄, x ∈ A → π g x ∈ A) → A ≠ ⊥ →
      ∃ x ∈ A, x ∈ fixed π K ∧ x ≠ 0) :
    ∃ (S : Subrepresentation π) (u : V), u ∈ S.toSubmodule ∧ u ≠ 0 ∧ u ∈ fixed π K ∧
      S.toRepresentation.IsIrreducible ∧ FiniteDimensional ℂ (fixed S.toRepresentation K) := by sorry
