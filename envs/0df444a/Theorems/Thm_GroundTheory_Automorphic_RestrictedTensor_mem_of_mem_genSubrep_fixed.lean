-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_mem_of_mem_genSubrep_fixed
-- name    : GroundTheory.Automorphic.RestrictedTensor.mem_of_mem_genSubrep_fixed
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:33:15.135827+00:00
-- url     : https://prove2.me/theorems/ac594411-e762-4120-a88d-8e62f13d7084
-- title:
--   Restricted Tensor: mem of mem gen Subrep fixed
-- statement:
--   The Restricted Tensor construction uses the mem of mem gen Subrep fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/LocalComponent.lean#L103-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/LocalComponent.lean#L103-L112

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

theorem GroundTheory.Automorphic.RestrictedTensor.mem_of_mem_genSubrep_fixed {u : V} (hu : u ∈ (genSubrep σ N).toSubmodule)
    (huK : u ∈ fixedVectors σ K) : u ∈ N := by sorry
