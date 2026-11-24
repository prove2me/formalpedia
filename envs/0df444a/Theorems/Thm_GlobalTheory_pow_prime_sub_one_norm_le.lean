-- Prove2me | Theorems.Thm_GlobalTheory_pow_prime_sub_one_norm_le
-- name    : GlobalTheory.pow_prime_sub_one_norm_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:14:13.110811+00:00
-- url     : https://prove2.me/theorems/c16c5851-f14d-4b7e-96df-e3361e1f1b55
-- title:
--   Global Theory: pow prime sub one norm le
-- statement:
--   The Global Theory construction uses the pow prime sub one norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PowPrimeSubOneNormLe.lean#L6-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PowPrimeSubOneNormLe.lean#L6-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixOneAddPowSubEntryLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PowPrimeSubOneNormLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.pow_prime_sub_one_norm_le : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (X : Matrix n n ℚ_[l]) (k : ℕ), (∀ i j, ‖(X - 1) i j‖ ≤ (l : ℝ) ^ (-((k : ℤ) + 2))) → ∀ i j, ‖(X ^ l - 1) i j‖ ≤ (l : ℝ) ^ (-(((k + 1 : ℕ) : ℤ) + 2)) := by sorry
