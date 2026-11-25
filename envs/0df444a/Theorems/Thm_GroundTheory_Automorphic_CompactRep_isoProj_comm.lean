-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_CompactRep_isoProj_comm
-- name    : GroundTheory.Automorphic.CompactRep.isoProj_comm
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:24:26.651396+00:00
-- url     : https://prove2.me/theorems/01c33887-4e00-45c2-90f2-60cdf719f156
-- title:
--   Compact Rep: iso Proj comm
-- statement:
--   The Compact Rep construction uses the iso Proj comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/KFinite.lean#L130-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/KFinite.lean#L130-L141

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

theorem GroundTheory.Automorphic.CompactRep.isoProj_comm {c : Submodule R M} (hc : c ∈ isotypicComponents R M) (f : Module.End R M)
    (x : M) : isoProj hc (f x) = f (isoProj hc x) := by sorry
