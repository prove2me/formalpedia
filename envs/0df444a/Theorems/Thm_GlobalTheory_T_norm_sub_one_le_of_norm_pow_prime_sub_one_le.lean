-- Prove2me | Theorems.Thm_GlobalTheory_T_norm_sub_one_le_of_norm_pow_prime_sub_one_le
-- name    : GlobalTheory.T.norm_sub_one_le_of_norm_pow_prime_sub_one_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:54:07.107774+00:00
-- url     : https://prove2.me/theorems/c1126fdc-2cba-4d80-979f-c1337ef4dec5
-- title:
--   T: norm sub one le of norm pow prime sub one le
-- statement:
--   The T construction uses the norm sub one le of norm pow prime sub one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixNearOnePowPrimeDeepStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixNearOnePowPrimeDeepStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixNearOnePowPrimeDeep
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixNearOnePowPrimeDeepStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.norm_sub_one_le_of_norm_pow_prime_sub_one_le : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (X : Matrix n n ℚ_[l]) (k : ℕ), (∀ i j, ‖(X - 1) i j‖ ≤ (l : ℝ) ^ (-2 : ℤ)) → (∀ i j, ‖(X ^ l - 1) i j‖ ≤ (l : ℝ) ^ (-(((k + 1 : ℕ) : ℤ) + 2))) → ∀ i j, ‖(X - 1) i j‖ ≤ (l : ℝ) ^ (-((k : ℤ) + 2)) := by sorry
