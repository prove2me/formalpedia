-- Prove2me | Theorems.Thm_GlobalTheory_rat_alternating_orthogonal_orthogonal_le
-- name    : GlobalTheory.rat_alternating_orthogonal_orthogonal_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:15:48.278392+00:00
-- url     : https://prove2.me/theorems/b2070bc4-b1d2-4313-9864-76e590c8e009
-- title:
--   Global Theory: rat alternating orthogonal orthogonal le
-- statement:
--   The Global Theory construction uses the rat alternating orthogonal orthogonal le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RatAlternatingOrthogonalOrthogonalLeAlt.lean#L6-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RatAlternatingOrthogonalOrthogonalLeAlt.lean#L6-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RatAlternatingOrthogonalOrthogonalLeAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory

theorem GlobalTheory.rat_alternating_orthogonal_orthogonal_le :
    ∀ (r : ℕ) (Mq : Matrix (Fin r) (Fin r) ℚ) (V : Submodule ℚ (Fin r → ℚ)), Mqᵀ = -Mq →
      Mq.det ≠ 0 → ∀ x : Fin r → ℚ,
      (∀ y : Fin r → ℚ, (∀ w ∈ V, y ⬝ᵥ Mq *ᵥ w = 0) → x ⬝ᵥ Mq *ᵥ y = 0) → x ∈ V := by sorry
