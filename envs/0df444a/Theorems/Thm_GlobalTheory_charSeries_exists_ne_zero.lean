-- Prove2me | Theorems.Thm_GlobalTheory_charSeries_exists_ne_zero
-- name    : GlobalTheory.charSeries_exists_ne_zero
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:07:50.161799+00:00
-- url     : https://prove2.me/theorems/4d4f110b-a76c-4c4a-bfa3-c6169e19ece1
-- title:
--   Global Theory: char Series exists ne zero
-- statement:
--   The Global Theory construction uses the char Series exists ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/CharSeriesExistsNeZero.lean#L53-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/CharSeriesExistsNeZero.lean#L53-L85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CharSeriesExistsNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open GlobalTheory

theorem GlobalTheory.charSeries_exists_ne_zero : ∀ (A I : Type) [AddCommGroup A] (e : I → A → ℂ) (c : I → ℂ) (i₀ : I), (∀ i a b, e i (a + b) = e i a * e i b) → (∀ i a, ‖e i a‖ ≤ 1) → (∀ a, e i₀ a = 1) → (∀ i, i ≠ i₀ → ∃ a, e i a = -1) → Summable (fun i => ‖c i‖) → c i₀ ≠ 0 → ∃ a, ∑' i, c i * e i a ≠ 0 := by sorry
