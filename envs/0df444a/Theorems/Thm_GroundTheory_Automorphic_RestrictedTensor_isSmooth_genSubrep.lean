-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_isSmooth_genSubrep
-- name    : GroundTheory.Automorphic.RestrictedTensor.isSmooth_genSubrep
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:46.673837+00:00
-- url     : https://prove2.me/theorems/a69c2f96-9372-4dc0-84f2-0991be254709
-- title:
--   Restricted Tensor: is Smooth gen Subrep
-- statement:
--   The Restricted Tensor construction uses the is Smooth gen Subrep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/LocalComponent.lean#L81-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/LocalComponent.lean#L81-L84

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
include hσ

theorem GroundTheory.Automorphic.RestrictedTensor.isSmooth_genSubrep : IsSmooth (genSubrep σ N).toRepresentation := by sorry
