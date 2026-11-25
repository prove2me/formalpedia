-- Prove2me | Theorems.Thm_GlobalTheory_prod_le_of_interlacing_pairing
-- name    : GlobalTheory.prod_le_of_interlacing_pairing
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:34:46.192132+00:00
-- url     : https://prove2.me/theorems/d41039d0-fae5-49f3-a4aa-57bace5d9909
-- title:
--   Global Theory: prod le of interlacing pairing
-- statement:
--   The Global Theory construction uses the prod le of interlacing pairing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ProdLeOfInterlacingPairing.lean#L7-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ProdLeOfInterlacingPairing.lean#L7-L94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ProdLeOfInterlacingPairing
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

theorem GlobalTheory.prod_le_of_interlacing_pairing :
    ∀ (k l : ℕ) (c B Y : ℝ) (lam v a : ℕ → ℝ), 0 ≤ c → 1 ≤ B → (∀ s : ℕ, 1 ≤ s → s + 1 ≤ k - 1 → lam (s + 1) ≤ lam s) → (∀ s : ℕ, 1 ≤ s → s + 1 ≤ k → (s ≠ l → lam s + 1 / 2 ≤ v s) ∧ (s + 1 ≠ l → v (s + 1) + 1 / 2 ≤ lam s)) → (∀ i ∈ Finset.Icc 1 k, 1 ≤ |Y + 1 / 2 + v i|) → (∀ s ∈ Finset.Icc 1 (k - 1), 0 ≤ a s ∧ a s ≤ |lam s + Y| + 1 + c ∧ a s ≤ B) → ∏ s ∈ Finset.Icc 1 (k - 1), a s ≤ B * (∏ s ∈ Finset.Icc 1 (k - 1), (1 + (1 + c) / max |lam s + Y| 1)) * ∏ i ∈ Finset.Icc 1 k, |Y + 1 / 2 + v i| := by sorry
