-- Prove2me | Theorems.Thm_GlobalTheory_mul_norm_sq_le_norm_proj_apply_sq_of_spanning_parts
-- name    : GlobalTheory.mul_norm_sq_le_norm_proj_apply_sq_of_spanning_parts
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:49:17.519886+00:00
-- url     : https://prove2.me/theorems/dcada95b-f466-489e-95f9-7e4677f8618b
-- title:
--   Global Theory: mul norm sq le norm proj apply sq of spanning parts
-- statement:
--   The Global Theory construction uses the mul norm sq le norm proj apply sq of spanning parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MulNormSqLeNormProjApplySqOfSpanningParts.lean#L61-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MulNormSqLeNormProjApplySqOfSpanningParts.lean#L61-L87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MulNormSqLeNormProjApplySqOfSpanningParts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open GlobalTheory

theorem GlobalTheory.mul_norm_sq_le_norm_proj_apply_sq_of_spanning_parts :
    ∀ (X Y ι : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X] [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (T : X →ₗ[ℂ] Y) (e : Y →ₗ[ℂ] Y) (P : ι → Submodule ℂ Y) (m : ℝ), 0 < m → LinearMap.adjoint e = e → (∀ y, e (e y) = e y) → (⨆ k, P k) = ⊤ → (∀ k, ∃ l : ℝ, m ≤ l ∧ ∀ y ∈ P k, T (LinearMap.adjoint T y) = (l : ℂ) • y) → ∀ x ∈ (LinearMap.ker (e ∘ₗ T))ᗮ, m * ‖x‖ ^ 2 ≤ ‖e (T x)‖ ^ 2 := by sorry
