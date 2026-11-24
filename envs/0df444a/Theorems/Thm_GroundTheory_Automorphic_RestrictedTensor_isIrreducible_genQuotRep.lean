-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_isIrreducible_genQuotRep
-- name    : GroundTheory.Automorphic.RestrictedTensor.isIrreducible_genQuotRep
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:33:11.241597+00:00
-- url     : https://prove2.me/theorems/3617c469-7815-4e7a-909e-6b4d4749c9b1
-- title:
--   Restricted Tensor: is Irreducible gen Quot Rep
-- statement:
--   The Restricted Tensor construction uses the is Irreducible gen Quot Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/LocalComponent.lean#L142-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/LocalComponent.lean#L142-L210

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Window
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_LocalComponent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.RestrictedTensor
open Module Set
variable {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [LocallyCompactSpace L] [T2Space L] [TotallyDisconnectedSpace L]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {σ : Representation ℂ L V}
variable (hσ : IsSmooth σ) {K : Subgroup L} (hKc : IsCompact (K : Set L))
  (hKo : IsOpen (K : Set L)) (N : Submodule ℂ V)
variable {N}
variable (hNK : N ≤ fixedVectors σ K)
  (hNst : ∀ g, ∀ n ∈ N, (fixedProj σ hσ hKc hKo (σ g n) : V) ∈ N)
include hNK hNst

theorem GroundTheory.Automorphic.RestrictedTensor.isIrreducible_genQuotRep (hN0 : N ≠ ⊥)
    (hNmin : ∀ N₁ : Submodule ℂ V, N₁ ≤ N → N₁ ≠ ⊥ →
      (∀ g, ∀ n ∈ N₁, (fixedProj σ hσ hKc hKo (σ g n) : V) ∈ N₁) → N₁ = N) :
    (genQuotRep hσ hKc hKo N).IsIrreducible := by sorry
