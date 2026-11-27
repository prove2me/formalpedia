-- Prove2me | Theorems.Thm_GlobalTheory_exists_rational_orthogonal_projection_of_finrank_le
-- name    : GlobalTheory.exists_rational_orthogonal_projection_of_finrank_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-27T05:30:29.36421+00:00
-- url     : https://prove2.me/theorems/ffdfe62c-d192-5f83-82f4-a8e3db19382f
-- title:
--   Global Theory: exists rational orthogonal projection of finrank le
-- statement:
--   The Global Theory construction uses the exists rational orthogonal projection of finrank le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRationalOrthogonalProjectionSemilinear.lean#L6-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRationalOrthogonalProjectionSemilinear.lean#L6-L70

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

theorem GlobalTheory.exists_rational_orthogonal_projection_of_finrank_le (K : Type) [Field K] (σ : K →+* ℂ) (W : Type)
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] (n : ℕ) (j : (Fin n → K) →ₛₗ[σ] W)
    (hj : ∀ x y, ⟪j x, j y⟫_ℂ ∈ Set.range σ) :
    ∀ (d : ℕ) (N : Submodule K (Fin n → K)), Module.finrank K N ≤ d → ∀ (x : Fin n → K),
      ∃ y ∈ N, ∀ m ∈ N, ⟪j m, j x - j y⟫_ℂ = 0 := by sorry
