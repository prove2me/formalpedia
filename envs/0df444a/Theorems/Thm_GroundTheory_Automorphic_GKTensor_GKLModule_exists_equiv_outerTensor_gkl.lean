-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GKTensor_GKLModule_exists_equiv_outerTensor_gkl
-- name    : GroundTheory.Automorphic.GKTensor.GKLModule.exists_equiv_outerTensor_gkl
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:58:54.516832+00:00
-- url     : https://prove2.me/theorems/2fa4d314-34e1-46bc-9b6d-80ee774934ae
-- title:
--   GKLModule: exists equiv outer Tensor gkl
-- statement:
--   The GKLModule construction uses the exists equiv outer Tensor gkl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/GKTensor.lean#L94-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/GKTensor.lean#L94-L164

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_CoeToRepresentationApply
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_KProjApplyEqSelfIff
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TwoFactorUnique
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Window
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_GKTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open GroundTheory GroundTheory.Automorphic
attribute [local instance 100] LieRing.ofAssociativeRing
open Set Module RestrictedTensor CompactRep
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.GKTensor
variable {h : IsExpLieAlgebra G 𝔤} {K : Subgroup G} [CompactSpace K]
open GroundTheory.Automorphic.GKTensor.GKLModule
variable {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L] [LocallyCompactSpace L]
  [T2Space L] [TotallyDisconnectedSpace L] {V : Type u} [AddCommGroup V] [Module ℂ V]
  (Mx : GKLModule h K L V)
set_option maxHeartbeats 2000000

theorem GroundTheory.Automorphic.GKTensor.GKLModule.exists_equiv_outerTensor_gkl (hirr : Mx.IsIrreducible) (hadm : Mx.IsAdmissible) :
    ∃ (H : Subgroup L) (hHc : IsCompact (H : Set L)) (hHo : IsOpen (H : Set L))
      (c : Submodule (MonoidAlgebra ℂ K) Mx.gk.σ.asModule)
      (hc : c ∈ isotypicComponents (MonoidAlgebra ℂ K) Mx.gk.σ.asModule) (N₁ N₂ : Submodule ℂ V),
      N₁ ≤ fixedVectors Mx.τ H ∧ N₂ ≤ fixedVectors Mx.τ H ∧
      N₂ ≤ LinearMap.range (kProj Mx.gk.isKFinite hc) ∧ N₁ ≠ ⊥ ∧ N₂ ≠ ⊥ ∧
      (∀ b, ∀ n ∈ N₂, fixedEnd hadm.1 hHc hHo (Mx.τ b n) ∈ N₂) ∧
      (mGenQuotRep Mx.gk.rep (kProj Mx.gk.isKFinite hc) N₁).IsIrreducible ∧
      (mGenQuotRep Mx.τ (fixedEnd hadm.1 hHc hHo) N₂).IsIrreducible ∧
      ((∀ T : End ℂ ((mGenSubrep Mx.τ N₂).toSubmodule ⧸ mGenKernel Mx.τ (fixedEnd hadm.1 hHc hHo) N₂),
          (∀ b, T * mGenQuotRep Mx.τ (fixedEnd hadm.1 hHc hHo) N₂ b =
            mGenQuotRep Mx.τ (fixedEnd hadm.1 hHc hHo) N₂ b * T) → ∃ c : ℂ, T = c • 1) →
        Nonempty (Mx.fullRep.Equiv
          (outerTensor (mGenQuotRep Mx.gk.rep (kProj Mx.gk.isKFinite hc) N₁)
            (mGenQuotRep Mx.τ (fixedEnd hadm.1 hHc hHo) N₂)))) := by sorry
