-- Prove2me | Theorems.Thm_GlobalTheory_dvd_of_period_of_dvd_sum_powersetCard
-- name    : GlobalTheory.dvd_of_period_of_dvd_sum_powersetCard
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:16:54.730901+00:00
-- url     : https://prove2.me/theorems/b0cdb1c6-c338-4f40-96d0-f59d92e44ab3
-- title:
--   Global Theory: dvd of period of dvd sum powerset Card
-- statement:
--   The Global Theory construction uses the dvd of period of dvd sum powerset Card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DvdOfPeriodOfDvdSumPowersetCard.lean#L184-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DvdOfPeriodOfDvdSumPowersetCard.lean#L184-L280

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardDvdSumOfInvariantOfCardStabilizerDvd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DvdOfPeriodOfDvdSumPowersetCard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Pointwise
open GlobalTheory
open PeriodDvd

theorem GlobalTheory.dvd_of_period_of_dvd_sum_powersetCard (q d : ℕ) (a : ℕ → ℤ) (hq : 2 ≤ q) (hd : 0 < d)
    (hinv : ∀ k l i : ℕ, k * q ^ i ≡ l [MOD q ^ d - 1] → a k = a l)
    (hsum : ∀ k s : ℕ, (d : ℤ) ∣ ∑ I ∈ (Finset.range d).powersetCard s, a (k * ∑ i ∈ I, q ^ i))
    (s e l : ℕ) (hse : s * e = d) (hl : l * q ^ e ≡ l [MOD q ^ d - 1]) : (s : ℤ) ∣ a l := by sorry
