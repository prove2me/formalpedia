-- Prove2me | Theorems.Thm_GlobalTheory_adjoin_matrix_reduced_of_charpoly_separable
-- name    : GlobalTheory.adjoin_matrix_reduced_of_charpoly_separable
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:05:49.868918+00:00
-- url     : https://prove2.me/theorems/1a124e27-8de6-4d38-a5f6-171fe6c3787a
-- title:
--   Global Theory: adjoin matrix reduced of charpoly separable
-- statement:
--   The Global Theory construction uses the adjoin matrix reduced of charpoly separable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdjoinMatrixReducedOfCharpolySeparable.lean#L6-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdjoinMatrixReducedOfCharpolySeparable.lean#L6-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdjoinMatrixReducedOfCharpolySeparable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open GlobalTheory

theorem GlobalTheory.adjoin_matrix_reduced_of_charpoly_separable :
    ∀ (K : Type) [Field K] (n : ℕ) (N : Matrix (Fin n) (Fin n) K), N.charpoly.Separable →
      ∀ g ∈ Algebra.adjoin K {N}, ∀ m : ℕ, g ^ m = 0 → g = 0 := by sorry
