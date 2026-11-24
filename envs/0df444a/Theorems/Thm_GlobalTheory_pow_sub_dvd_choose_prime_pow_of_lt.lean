-- Prove2me | Theorems.Thm_GlobalTheory_pow_sub_dvd_choose_prime_pow_of_lt
-- name    : GlobalTheory.pow_sub_dvd_choose_prime_pow_of_lt
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:13:53.604714+00:00
-- url     : https://prove2.me/theorems/6ec9d270-5db9-4b55-b45a-adaf69233995
-- title:
--   Global Theory: pow sub dvd choose prime pow of lt
-- statement:
--   The Global Theory construction uses the pow sub dvd choose prime pow of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PowSubDvdChoosePrimePowOfLt.lean#L6-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PowSubDvdChoosePrimePowOfLt.lean#L6-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PowSubDvdChoosePrimePowOfLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open GlobalTheory

theorem GlobalTheory.pow_sub_dvd_choose_prime_pow_of_lt :
    ∀ (l a c i : ℕ), l.Prime → 1 ≤ i → i < l ^ (c + 1) → l ^ (a - c) ∣ (l ^ a).choose i := by sorry
