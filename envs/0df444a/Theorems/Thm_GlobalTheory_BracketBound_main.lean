-- Prove2me | Theorems.Thm_GlobalTheory_BracketBound_main
-- name    : GlobalTheory.BracketBound.main
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:09:39.939801+00:00
-- url     : https://prove2.me/theorems/00d7cf12-3705-43bd-adb8-e512b8923938
-- title:
--   Bracket Bound: main
-- statement:
--   The Bracket Bound construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/InterlacedShiftedDistanceBracketBound.lean#L8-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/InterlacedShiftedDistanceBracketBound.lean#L8-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SideSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ProdLeOfInterlacingPairing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_InterlacedShiftedDistanceBracketBound
import Theorems.Thm_GlobalTheory_CloudProd_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.BracketBound

theorem GlobalTheory.BracketBound.main : ∀ (k r l : ℕ) (b c Y e : ℝ) (lam v : ℕ → ℝ), 1 ≤ k → 1 ≤ c → c + 2 ≤ b → (k : ℝ) ≤ b → |Y| ≤ b → 0 ≤ e → e ≤ 1 → (∀ s ∈ Finset.Icc 1 (k + 2 * r + 1), |lam s| ≤ b) → (∀ s : ℕ, 1 ≤ s → s + 1 ≤ k - 1 → lam (s + 1) + 2 * c ≤ lam s) → (∀ s : ℕ, 1 ≤ s → s + 1 ≤ k → (s ≠ l → lam s + 1 / 2 ≤ v s) ∧ (s + 1 ≠ l → v (s + 1) + 1 / 2 ≤ lam s)) → (∀ i ∈ Finset.Icc 1 k, 1 ≤ |Y + 1 / 2 + v i|) → ∏ s ∈ Finset.Icc 1 (k + 2 * r + 1), (|Y + e + lam s| + c) ≤ b ^ (4 * r + 10) * ∏ i ∈ Finset.Icc 1 k, |Y + 1 / 2 + v i| := by sorry
