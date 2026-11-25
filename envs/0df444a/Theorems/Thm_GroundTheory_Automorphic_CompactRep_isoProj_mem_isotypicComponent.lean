-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_CompactRep_isoProj_mem_isotypicComponent
-- name    : GroundTheory.Automorphic.CompactRep.isoProj_mem_isotypicComponent
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:24:53.488425+00:00
-- url     : https://prove2.me/theorems/9f9e079e-04c7-4c80-a1b5-f495c604bed9
-- title:
--   Compact Rep: iso Proj mem isotypic Component
-- statement:
--   The Compact Rep construction uses the iso Proj mem isotypic Component property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/KFinite.lean#L122-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/KFinite.lean#L122-L124

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

theorem GroundTheory.Automorphic.CompactRep.isoProj_mem_isotypicComponent {c : Submodule R M} (hc : c ∈ isotypicComponents R M)
    (x : M) : isoProj hc x ∈ c := by sorry
