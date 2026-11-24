-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ProdSub_exists_irreducible_sub_inl
-- name    : GlobalTheory.CompanionTheory.ProdSub.exists_irreducible_sub_inl
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:56:40.560832+00:00
-- url     : https://prove2.me/theorems/32c5c3bc-ebb3-4770-a8db-2c3db1c01253
-- title:
--   Prod Sub: exists irreducible sub inl
-- statement:
--   The Prod Sub construction uses the exists irreducible sub inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsIrreducibleOfFixed.lean#L255-L328
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsIrreducibleOfFixed.lean#L255-L328

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsIrreducibleOfFixed
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp

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

theorem GlobalTheory.CompanionTheory.ProdSub.exists_irreducible_sub_inl : ∀ {G H V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup V] [Module ℂ V], (∀ U ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) → (∀ U ∈ 𝓝 (1 : H), ∃ K : Subgroup H, IsOpen (K : Set H) ∧ IsCompact (K : Set H) ∧ (K : Set H) ⊆ U) → ∀ ρ : Representation ℂ (G × H) V, IsAdmissible ρ → ρ.IsIrreducible → ∃ (K : Subgroup G) (S : Subrepresentation (ρ.comp (MonoidHom.inl G H))) (u : V), IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ u ∈ S.toSubmodule ∧ u ≠ 0 ∧ (∀ x ∈ K, ρ (x, 1) u = u) ∧ S.toRepresentation.IsIrreducible ∧ FiniteDimensional ℂ (fixed S.toRepresentation K) := by sorry
