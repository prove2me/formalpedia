-- Prove2me | Theorems.Thm_GlobalTheory_T_eq_zero_of_pow_eq_zero_of_mem_adjoin_of_charpoly_separable
-- name    : GlobalTheory.T.eq_zero_of_pow_eq_zero_of_mem_adjoin_of_charpoly_separable
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:28:20.564188+00:00
-- url     : https://prove2.me/theorems/155ca5bd-b185-4ab3-9e83-077189ed4df2
-- title:
--   T: eq zero of pow eq zero of mem adjoin of charpoly separable
-- statement:
--   The T construction uses the eq zero of pow eq zero of mem adjoin of charpoly separable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdjoinMatrixReducedOfCharpolySeparableStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdjoinMatrixReducedOfCharpolySeparableStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdjoinMatrixReducedOfCharpolySeparable
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdjoinMatrixReducedOfCharpolySeparableStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.eq_zero_of_pow_eq_zero_of_mem_adjoin_of_charpoly_separable : ∀ (K : Type) [Field K] (n : ℕ) (N : Matrix (Fin n) (Fin n) K), N.charpoly.Separable → ∀ g ∈ Algebra.adjoin K {N}, ∀ m : ℕ, g ^ m = 0 → g = 0 := by sorry
