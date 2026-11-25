-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_genQuotForm_apply
-- name    : GroundTheory.Automorphic.RestrictedTensor.genQuotForm_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:34:17.245859+00:00
-- url     : https://prove2.me/theorems/21dc6174-8aad-4e94-af63-09f9342eda90
-- title:
--   Restricted Tensor: gen Quot Form apply
-- statement:
--   The Restricted Tensor construction uses the gen Quot Form apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/LocalComponent.lean#L233-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/LocalComponent.lean#L233-L237

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

theorem GroundTheory.Automorphic.RestrictedTensor.genQuotForm_apply (l : Dual ℂ (fixedVectors σ K)) (hNK : N ≤ fixedVectors σ K) (g : L)
    (n : N) :
    genQuotForm hσ hKc hKo l (genQuotRep hσ hKc hKo N g (genQuotMk hσ hKc hKo N n)) =
      l (fixedProj σ hσ hKc hKo (σ g n)) := by sorry
