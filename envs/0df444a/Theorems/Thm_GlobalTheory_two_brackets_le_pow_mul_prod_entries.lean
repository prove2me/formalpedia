-- Prove2me | Theorems.Thm_GlobalTheory_two_brackets_le_pow_mul_prod_entries
-- name    : GlobalTheory.two_brackets_le_pow_mul_prod_entries
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:34:35.910018+00:00
-- url     : https://prove2.me/theorems/577c630d-636e-5b37-8b15-7d30ddd18214
-- title:
--   Global Theory: two brackets le pow mul prod entries
-- statement:
--   The Global Theory construction uses the two brackets le pow mul prod entries property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/TwoBracketsLePowMulProdEntries.lean#L279-L291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/TwoBracketsLePowMulProdEntries.lean#L279-L291

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_InterlacedShiftedDistanceBracketBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_TwoBracketsLePowMulProdEntries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory
open Finset

theorem GlobalTheory.two_brackets_le_pow_mul_prod_entries : ∀ (k r l : ℕ) (b c Y : ℝ) (lam u u' : ℕ → ℝ), 1 ≤ l → l ≤ k → 1 ≤ c → c + 2 ≤ b → (k : ℝ) ≤ b → |u l| ≤ b → |u' l| ≤ b → (∀ s ∈ Finset.Icc 1 (k + 2 * r + 1), |lam s| ≤ b) → (∀ s : ℕ, 1 ≤ s → s + 1 ≤ k - 1 → lam (s + 1) + 2 * c ≤ lam s) → (∀ s : ℕ, 1 ≤ s → s + 1 ≤ k → (s ≠ l → lam s + 1 / 2 ≤ u s) ∧ (s + 1 ≠ l → u (s + 1) + 1 / 2 ≤ lam s)) → (∀ s : ℕ, 1 ≤ s → s + 1 ≤ k → (s ≠ l → lam s + 1 / 2 ≤ u' s) ∧ (s + 1 ≠ l → u' (s + 1) + 1 / 2 ≤ lam s)) → (∀ i : ℕ, 1 ≤ i → i ≤ k - 1 → u (i + 1) ≤ u i - 1 ∧ u' (i + 1) ≤ u' i - 1 ∧ u (i + 1) ≤ u' i - 1 ∧ u' (i + 1) ≤ u i - 1) → ((u l + 2 ≤ -Y ∧ -Y ≤ u' l - 2) ∨ (u' l + 2 ≤ -Y ∧ -Y ≤ u l - 2)) → (∏ s ∈ Finset.Icc 1 (k + 2 * r + 1), (|Y + lam s| + c)) * (∏ s ∈ Finset.Icc 1 (k + 2 * r + 1), (|Y + 1 + lam s| + c)) ≤ b ^ (11 * (2 * r + 2)) * ∏ i ∈ Finset.Icc 1 k, |(Y + 1 / 2 + u i) * (Y + 1 / 2 + u' i)| := by sorry
