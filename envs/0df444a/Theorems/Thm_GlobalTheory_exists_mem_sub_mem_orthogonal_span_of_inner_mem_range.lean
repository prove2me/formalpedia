-- Prove2me | Theorems.Thm_GlobalTheory_exists_mem_sub_mem_orthogonal_span_of_inner_mem_range
-- name    : GlobalTheory.exists_mem_sub_mem_orthogonal_span_of_inner_mem_range
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-27T05:30:41.259801+00:00
-- url     : https://prove2.me/theorems/9bb62ea2-dfb7-43a5-9965-b7fabfd21eef
-- title:
--   Global Theory: exists mem sub mem orthogonal span of inner mem range
-- statement:
--   The Global Theory construction uses the exists mem sub mem orthogonal span of inner mem range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRationalOrthogonalProjectionSemilinear.lean#L72-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRationalOrthogonalProjectionSemilinear.lean#L72-L84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRationalOrthogonalProjectionSemilinear
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

theorem GlobalTheory.exists_mem_sub_mem_orthogonal_span_of_inner_mem_range : ∀ (K : Type) [Field K] (σ : K →+* ℂ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (n : ℕ) (j : (Fin n → K) →ₛₗ[σ] W), (∀ x y, ⟪j x, j y⟫_ℂ ∈ Set.range σ) → ∀ (N : Submodule K (Fin n → K)) (x : Fin n → K), ∃ y ∈ N, j x - j y ∈ (Submodule.span ℂ (j '' (N : Set (Fin n → K))))ᗮ := by sorry
