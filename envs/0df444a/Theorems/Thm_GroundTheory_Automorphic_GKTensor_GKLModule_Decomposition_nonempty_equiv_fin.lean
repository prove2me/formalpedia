-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GKTensor_GKLModule_Decomposition_nonempty_equiv_fin
-- name    : GroundTheory.Automorphic.GKTensor.GKLModule.Decomposition.nonempty_equiv_fin
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:58:14.534466+00:00
-- url     : https://prove2.me/theorems/c1ab7a78-b888-5660-babc-d1fb8c37635f
-- title:
--   Decomposition: nonempty equiv fin
-- statement:
--   The Decomposition construction uses the nonempty equiv fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/GKMain.lean#L271-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/GKMain.lean#L271-L273

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_GKTensor
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_GKMain
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
open Set Module RestrictedTensor CompactRep TensorProduct
open scoped TensorProduct
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} {h : IsExpLieAlgebra G 𝔤} {K : Subgroup G}
  [CompactSpace K]
open GroundTheory.Automorphic.GKTensor
variable {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L] [LocallyCompactSpace L]
  [T2Space L] [TotallyDisconnectedSpace L] {V : Type u} [AddCommGroup V] [Module ℂ V]
open GroundTheory.Automorphic.GKTensor.GKLModule
variable (Mx : GKLModule h K L V)
attribute [instance] Decomposition.instAddCommGroup₁ Decomposition.instModule₁
  Decomposition.instAddCommGroup₂ Decomposition.instModule₂
open GroundTheory.Automorphic.GKTensor.GKLModule.Decomposition
variable {Mx}

theorem GroundTheory.Automorphic.GKTensor.GKLModule.Decomposition.nonempty_equiv_fin (D D' : Mx.Decomposition) : Nonempty (D.π₂.Equiv D'.π₂) := by sorry
