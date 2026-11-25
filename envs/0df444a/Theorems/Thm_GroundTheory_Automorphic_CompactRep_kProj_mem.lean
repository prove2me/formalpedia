-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_CompactRep_kProj_mem
-- name    : GroundTheory.Automorphic.CompactRep.kProj_mem
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T01:07:12.025933+00:00
-- url     : https://prove2.me/theorems/f9b6a77c-6e4d-4941-9753-7febf2357203
-- title:
--   Compact Rep: k Proj mem
-- statement:
--   The Compact Rep construction uses the k Proj mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/KProjApplyEqSelfIff.lean#L54-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/KProjApplyEqSelfIff.lean#L54-L58

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

theorem GroundTheory.Automorphic.CompactRep.kProj_mem {Y : Submodule ℂ X} (hY : ∀ k, ∀ y ∈ Y, σ k y ∈ Y) {y : X} (hy : y ∈ Y) :
    kProj hσ hc y ∈ Y := by sorry
