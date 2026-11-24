-- Prove2me | Theorems.Thm_GlobalTheory_mul_norm_sq_le_norm_adjoint_sq_of_spanning_parts
-- name    : GlobalTheory.mul_norm_sq_le_norm_adjoint_sq_of_spanning_parts
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:12:59.410502+00:00
-- url     : https://prove2.me/theorems/cb92a9e7-7b57-45c4-bc0b-40ddef833051
-- title:
--   Global Theory: mul norm sq le norm adjoint sq of spanning parts
-- statement:
--   The Global Theory construction uses the mul norm sq le norm adjoint sq of spanning parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MulNormSqLeNormProjApplySqOfSpanningParts.lean#L6-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MulNormSqLeNormProjApplySqOfSpanningParts.lean#L6-L59

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

theorem GlobalTheory.mul_norm_sq_le_norm_adjoint_sq_of_spanning_parts
    {X Y ι : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y]
    (T : X →ₗ[ℂ] Y) (P : ι → Submodule ℂ Y) (m : ℝ) (hP : (⨆ k, P k) = ⊤)
    (hl : ∀ k, ∃ l : ℝ, m ≤ l ∧ ∀ y ∈ P k, T (LinearMap.adjoint T y) = (l : ℂ) • y) (u : Y) :
    m * ‖u‖ ^ 2 ≤ ‖LinearMap.adjoint T u‖ ^ 2 := by sorry
