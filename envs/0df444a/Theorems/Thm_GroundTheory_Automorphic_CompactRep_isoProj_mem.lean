-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_CompactRep_isoProj_mem
-- name    : GroundTheory.Automorphic.CompactRep.isoProj_mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:27:30.255821+00:00
-- url     : https://prove2.me/theorems/4da91544-6451-427a-9c88-ff3ad868f902
-- title:
--   Compact Rep: iso Proj mem
-- statement:
--   The Compact Rep construction uses the iso Proj mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/KFinite.lean#L143-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/KFinite.lean#L143-L149

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_CompactRep
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_MatrixCoeff
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_KFinite
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
open GroundTheory.Automorphic.CompactRep
open Module Set
variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [T2Space K] {X : Type*} [AddCommGroup X] [Module ℂ X]
variable {σ : Representation ℂ K X}
variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [IsSemisimpleModule R M]

theorem GroundTheory.Automorphic.CompactRep.isoProj_mem {c : Submodule R M} (hc : c ∈ isotypicComponents R M) (Y : Submodule R M)
    {y : M} (hy : y ∈ Y) : isoProj hc y ∈ Y := by sorry
