-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_genQuotRep_mk
-- name    : GroundTheory.Automorphic.RestrictedTensor.genQuotRep_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:54.94151+00:00
-- url     : https://prove2.me/theorems/2e7428dd-9d47-4137-88ec-68d10d674f31
-- title:
--   Restricted Tensor: gen Quot Rep mk
-- statement:
--   The Restricted Tensor construction uses the gen Quot Rep mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/LocalComponent.lean#L70-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/LocalComponent.lean#L70-L73

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

theorem GroundTheory.Automorphic.RestrictedTensor.genQuotRep_mk (g : L) (u : (genSubrep σ N).toSubmodule) :
    genQuotRep hσ hKc hKo N g (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk ((genSubrep σ N).toRepresentation g u) := by sorry
