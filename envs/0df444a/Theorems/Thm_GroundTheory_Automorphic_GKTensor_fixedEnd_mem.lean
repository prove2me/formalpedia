-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GKTensor_fixedEnd_mem
-- name    : GroundTheory.Automorphic.GKTensor.fixedEnd_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:31:40.714116+00:00
-- url     : https://prove2.me/theorems/a8099900-e52c-4505-ac44-56355c07320b
-- title:
--   GKTensor: fixed End mem
-- statement:
--   The GKTensor construction uses the fixed End mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/GKTensor.lean#L35-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/GKTensor.lean#L35-L36

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
variable {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L] [LocallyCompactSpace L]
  [T2Space L] [TotallyDisconnectedSpace L]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {τ : Representation ℂ L V} (hτ : IsSmooth τ)
  {H : Subgroup L} (hHc : IsCompact (H : Set L)) (hHo : IsOpen (H : Set L))

theorem GroundTheory.Automorphic.GKTensor.fixedEnd_mem (v : V) : fixedEnd hτ hHc hHo v ∈ fixedVectors τ H := by sorry
