-- Prove2me | Theorems.Thm_GlobalTheory_OrthogonalProjection_exists_orth_proj
-- name    : GlobalTheory.OrthogonalProjection.exists_orth_proj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:02.651326+00:00
-- url     : https://prove2.me/theorems/8eb3827d-e744-4759-b770-e855149c1690
-- title:
--   Orthogonal Projection: exists orth proj
-- statement:
--   The Orthogonal Projection construction uses the exists orth proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsOrthogonalProjectionFinite.lean#L42-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsOrthogonalProjectionFinite.lean#L42-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsOrthogonalProjectionFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.OrthogonalProjection
open Module

theorem GlobalTheory.OrthogonalProjection.exists_orth_proj : ∀ {W : Type} [inst : AddCommGroup W] [inst_1 : Module ℂ W] (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ), (∀ (v : W), ((B : W → W →ₗ[ℂ] ℂ) v : W → ℂ) v = (0 : ℂ) → v = (0 : W)) → ∀ (M : Submodule ℂ W) [FiniteDimensional ℂ ↥M] (v : W), ∃ m ∈ M, ∀ z ∈ M, ((B : W → W →ₗ[ℂ] ℂ) z : W → ℂ) (v - m) = (0 : ℂ) := by sorry
