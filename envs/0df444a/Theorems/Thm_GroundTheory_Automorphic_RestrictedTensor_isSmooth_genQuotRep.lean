-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_isSmooth_genQuotRep
-- name    : GroundTheory.Automorphic.RestrictedTensor.isSmooth_genQuotRep
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:33:39.215447+00:00
-- url     : https://prove2.me/theorems/f5463942-6332-48bd-8a6a-39dd85d78937
-- title:
--   Restricted Tensor: is Smooth gen Quot Rep
-- statement:
--   The Restricted Tensor construction uses the is Smooth gen Quot Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/LocalComponent.lean#L86-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/LocalComponent.lean#L86-L92

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

theorem GroundTheory.Automorphic.RestrictedTensor.isSmooth_genQuotRep : IsSmooth (genQuotRep hσ hKc hKo N) := by sorry
