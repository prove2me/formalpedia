-- Prove2me | Theorems.Thm_GlobalTheory_OrthogonalProjection_exists_orthogonal_projection_finite
-- name    : GlobalTheory.OrthogonalProjection.exists_orthogonal_projection_finite
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:38:41.722939+00:00
-- url     : https://prove2.me/theorems/ae114caf-cf43-4516-8efe-a48ecc79d756
-- title:
--   Orthogonal Projection: exists orthogonal projection finite
-- statement:
--   The Orthogonal Projection construction uses the exists orthogonal projection finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsOrthogonalProjectionFinite.lean#L7-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsOrthogonalProjectionFinite.lean#L7-L40

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

theorem GlobalTheory.OrthogonalProjection.exists_orthogonal_projection_finite {W : Type} [AddCommGroup W] [Module ℂ W] (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ)
    (hB : ∀ v : W, B v v = 0 → v = 0) (M : Submodule ℂ W) [FiniteDimensional ℂ M] (v : W) :
    ∃ m ∈ M, ∀ z ∈ M, B z (v - m) = 0 := by sorry
