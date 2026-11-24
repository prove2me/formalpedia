-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ProdSub_exists_fixed_of_ne_bot
-- name    : GlobalTheory.CompanionTheory.ProdSub.exists_fixed_of_ne_bot
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:56:35.890059+00:00
-- url     : https://prove2.me/theorems/8e461049-d400-4596-a861-9b9d9b533eab
-- title:
--   Prod Sub: exists fixed of ne bot
-- statement:
--   The Prod Sub construction uses the exists fixed of ne bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsIrreducibleOfFixed.lean#L168-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsIrreducibleOfFixed.lean#L168-L251

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
variable {G H V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [AddCommGroup V] [Module ℂ V]

theorem GlobalTheory.CompanionTheory.ProdSub.exists_fixed_of_ne_bot (ρ : Representation ℂ (G × H) V) (hi : ρ.IsIrreducible)
    (hs : IsSmooth (ρ.comp (MonoidHom.inl G H))) {K : Subgroup G} (hK : IsCompact (K : Set G))
    {v : V} (hv : v ≠ 0) (hvK : v ∈ fixed (ρ.comp (MonoidHom.inl G H)) K)
    (A : Submodule ℂ V) (hA : ∀ g, ∀ ⦃x⦄, x ∈ A → (ρ.comp (MonoidHom.inl G H)) g x ∈ A) (hA0 : A ≠ ⊥) :
    ∃ x ∈ A, x ∈ fixed (ρ.comp (MonoidHom.inl G H)) K ∧ x ≠ 0 := by sorry
