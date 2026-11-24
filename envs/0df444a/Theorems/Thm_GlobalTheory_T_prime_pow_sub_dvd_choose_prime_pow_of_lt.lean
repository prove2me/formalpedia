-- Prove2me | Theorems.Thm_GlobalTheory_T_prime_pow_sub_dvd_choose_prime_pow_of_lt
-- name    : GlobalTheory.T.prime_pow_sub_dvd_choose_prime_pow_of_lt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:54:45.641339+00:00
-- url     : https://prove2.me/theorems/64b0ccb2-16c2-45db-b5b9-668049acf3e8
-- title:
--   T: prime pow sub dvd choose prime pow of lt
-- statement:
--   The T construction uses the prime pow sub dvd choose prime pow of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PowSubDvdChoosePrimePowOfLtStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PowSubDvdChoosePrimePowOfLtStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PowSubDvdChoosePrimePowOfLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PowSubDvdChoosePrimePowOfLtStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.prime_pow_sub_dvd_choose_prime_pow_of_lt : ∀ (l a c i : ℕ), l.Prime → 1 ≤ i → i < l ^ (c + 1) → l ^ (a - c) ∣ (l ^ a).choose i := by sorry
