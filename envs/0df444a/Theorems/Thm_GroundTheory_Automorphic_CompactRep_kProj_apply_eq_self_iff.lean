-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_CompactRep_kProj_apply_eq_self_iff
-- name    : GroundTheory.Automorphic.CompactRep.kProj_apply_eq_self_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T01:07:08.22905+00:00
-- url     : https://prove2.me/theorems/1009245b-be54-423b-a2a3-f3011111b97b
-- title:
--   Compact Rep: k Proj apply eq self iff
-- statement:
--   The Compact Rep construction uses the k Proj apply eq self iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/KProjApplyEqSelfIff.lean#L25-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/KProjApplyEqSelfIff.lean#L25-L32

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_KFinite
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_GenWindow
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_KProjApplyEqSelfIff
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
open Module Set RestrictedTensor
variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [T2Space K] {X : Type*} [AddCommGroup X] [Module ℂ X] {σ : Representation ℂ K X}
variable (hσ : IsKFinite σ) {c : Submodule (MonoidAlgebra ℂ K) σ.asModule}
  (hc : c ∈ isotypicComponents (MonoidAlgebra ℂ K) σ.asModule)

theorem GroundTheory.Automorphic.CompactRep.kProj_apply_eq_self_iff {v : X} : kProj hσ hc v = v ↔ (v : σ.asModule) ∈ c := by sorry
