-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_CompactRep_kProj_mem_component
-- name    : GroundTheory.Automorphic.CompactRep.kProj_mem_component
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T01:08:29.209002+00:00
-- url     : https://prove2.me/theorems/08d281a8-016d-4779-b41c-b7668ff090c7
-- title:
--   Compact Rep: k Proj mem component
-- statement:
--   The Compact Rep construction uses the k Proj mem component property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/KProjApplyEqSelfIff.lean#L34-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/KProjApplyEqSelfIff.lean#L34-L36

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

theorem GroundTheory.Automorphic.CompactRep.kProj_mem_component (v : X) : (kProj hσ hc v : σ.asModule) ∈ c := by sorry
