-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GKTensor_isSmooth_mGenSubrep
-- name    : GroundTheory.Automorphic.GKTensor.isSmooth_mGenSubrep
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:39:37.038412+00:00
-- url     : https://prove2.me/theorems/3107bfe0-8ffa-4099-871f-ac62cc9b2015
-- title:
--   GKTensor: is Smooth m Gen Subrep
-- statement:
--   The GKTensor construction uses the is Smooth m Gen Subrep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/GKMain.lean#L34-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/GKMain.lean#L34-L38

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
  [T2Space L] [TotallyDisconnectedSpace L] {V : Type*} [AddCommGroup V] [Module ℂ V]
  {τ : Representation ℂ L V}

theorem GroundTheory.Automorphic.GKTensor.isSmooth_mGenSubrep (hτ : IsSmooth τ) (N : Submodule ℂ V) :
    IsSmooth (mGenSubrep τ N).toRepresentation := by sorry
