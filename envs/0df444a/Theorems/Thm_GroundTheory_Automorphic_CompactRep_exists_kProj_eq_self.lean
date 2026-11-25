-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_CompactRep_exists_kProj_eq_self
-- name    : GroundTheory.Automorphic.CompactRep.exists_kProj_eq_self
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T01:08:15.4738+00:00
-- url     : https://prove2.me/theorems/23c0b6ab-9300-4b70-935e-08eacdba39b7
-- title:
--   Compact Rep: exists k Proj eq self
-- statement:
--   The Compact Rep construction uses the exists k Proj eq self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/KProjApplyEqSelfIff.lean#L65-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/KProjApplyEqSelfIff.lean#L65-L84

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

theorem GroundTheory.Automorphic.CompactRep.exists_kProj_eq_self {Y : Submodule ℂ X} (hY : ∀ k, ∀ y ∈ Y, σ k y ∈ Y) (hY0 : Y ≠ ⊥) :
    ∃ (c : Submodule (MonoidAlgebra ℂ K) σ.asModule)
      (hc : c ∈ isotypicComponents (MonoidAlgebra ℂ K) σ.asModule),
      ∃ y ∈ Y, y ≠ 0 ∧ kProj hσ hc y = y := by sorry
