-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ProdSub_fixed_sup_eq_zero
-- name    : GlobalTheory.CompanionTheory.ProdSub.fixed_sup_eq_zero
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:56:31.774381+00:00
-- url     : https://prove2.me/theorems/b0a7be49-fc47-44da-8fdd-4b0f7fe2038a
-- title:
--   Prod Sub: fixed sup eq zero
-- statement:
--   The Prod Sub construction uses the fixed sup eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsIrreducibleOfFixed.lean#L20-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsIrreducibleOfFixed.lean#L20-L55

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

theorem GlobalTheory.CompanionTheory.ProdSub.fixed_sup_eq_zero [TopologicalSpace G] [IsTopologicalGroup G] {π : Representation ℂ G V}
    (hπ : IsSmooth π) {K : Subgroup G} (hK : IsCompact (K : Set G)) {A B : Submodule ℂ V}
    (hA : ∀ g, ∀ ⦃x⦄, x ∈ A → π g x ∈ A) (hB : ∀ g, ∀ ⦃x⦄, x ∈ B → π g x ∈ B)
    (hA0 : ∀ x ∈ A, x ∈ fixed π K → x = 0) (hB0 : ∀ x ∈ B, x ∈ fixed π K → x = 0)
    {x : V} (hx : x ∈ A ⊔ B) (hf : x ∈ fixed π K) : x = 0 := by sorry
