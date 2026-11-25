-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_CompactRep_isoProj_apply_of_mem_compl
-- name    : GroundTheory.Automorphic.CompactRep.isoProj_apply_of_mem_compl
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:26:42.774796+00:00
-- url     : https://prove2.me/theorems/1327eac4-8638-4ea2-9237-53a662147563
-- title:
--   Compact Rep: iso Proj apply of mem compl
-- statement:
--   The Compact Rep construction uses the iso Proj apply of mem compl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/KFinite.lean#L126-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/KFinite.lean#L126-L128

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

theorem GroundTheory.Automorphic.CompactRep.isoProj_apply_of_mem_compl {c : Submodule R M} (hc : c ∈ isotypicComponents R M) {x : M}
    (hx : x ∈ sSup (isotypicComponents R M \ {c})) : isoProj hc x = 0 := by sorry
