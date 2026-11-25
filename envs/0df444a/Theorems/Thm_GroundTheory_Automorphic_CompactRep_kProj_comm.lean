-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_CompactRep_kProj_comm
-- name    : GroundTheory.Automorphic.CompactRep.kProj_comm
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:07:54.861702+00:00
-- url     : https://prove2.me/theorems/0e2cde30-7f85-4efb-9cb2-362048ab108f
-- title:
--   Compact Rep: k Proj comm
-- statement:
--   The Compact Rep construction uses the k Proj comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/KProjApplyEqSelfIff.lean#L48-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/KProjApplyEqSelfIff.lean#L48-L52

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

theorem GroundTheory.Automorphic.CompactRep.kProj_comm {T : End ℂ X} (hT : ∀ k, T * σ k = σ k * T) (v : X) :
    kProj hσ hc (T v) = T (kProj hσ hc v) := by sorry
