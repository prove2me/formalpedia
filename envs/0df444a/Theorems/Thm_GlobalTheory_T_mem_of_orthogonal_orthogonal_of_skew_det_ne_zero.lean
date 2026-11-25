-- Prove2me | Theorems.Thm_GlobalTheory_T_mem_of_orthogonal_orthogonal_of_skew_det_ne_zero
-- name    : GlobalTheory.T.mem_of_orthogonal_orthogonal_of_skew_det_ne_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:35:28.432241+00:00
-- url     : https://prove2.me/theorems/d328f70a-2370-415b-b44d-5c3c07ed6b43
-- title:
--   T: mem of orthogonal orthogonal of skew det ne zero
-- statement:
--   The T construction uses the mem of orthogonal orthogonal of skew det ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RatAlternatingOrthogonalOrthogonalLeStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RatAlternatingOrthogonalOrthogonalLeStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RatAlternatingOrthogonalOrthogonalLeAlt
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RatAlternatingOrthogonalOrthogonalLeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.mem_of_orthogonal_orthogonal_of_skew_det_ne_zero : ∀ (r : ℕ) (Mq : Matrix (Fin r) (Fin r) ℚ) (V : Submodule ℚ (Fin r → ℚ)), Mqᵀ = -Mq → Mq.det ≠ 0 → ∀ x : Fin r → ℚ, (∀ y : Fin r → ℚ, (∀ w ∈ V, y ⬝ᵥ Mq *ᵥ w = 0) → x ⬝ᵥ Mq *ᵥ y = 0) → x ∈ V := by sorry
