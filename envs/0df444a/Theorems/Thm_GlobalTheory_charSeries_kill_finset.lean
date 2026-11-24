-- Prove2me | Theorems.Thm_GlobalTheory_charSeries_kill_finset
-- name    : GlobalTheory.charSeries_kill_finset
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:07:24.54509+00:00
-- url     : https://prove2.me/theorems/fb965e4b-5647-42a3-aac3-dfc0ce35da7f
-- title:
--   Global Theory: char Series kill finset
-- statement:
--   The Global Theory construction uses the char Series kill finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/CharSeriesExistsNeZero.lean#L7-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/CharSeriesExistsNeZero.lean#L7-L51

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

theorem GlobalTheory.charSeries_kill_finset {A I : Type} [AddCommGroup A] (e : I → A → ℂ) (c : I → ℂ) (i₀ : I)
    (hmul : ∀ i a b, e i (a + b) = e i a * e i b) (hle : ∀ i a, ‖e i a‖ ≤ 1)
    (h0 : ∀ a, e i₀ a = 1) (hneg : ∀ i, i ≠ i₀ → ∃ a, e i a = -1)
    (hs : Summable (fun i => ‖c i‖)) (hF : ∀ a, ∑' i, c i * e i a = 0) (s : Finset I) :
    ∃ c' : I → ℂ, c' i₀ = c i₀ ∧ (∀ i ∈ s, i ≠ i₀ → c' i = 0) ∧ (∀ i, ‖c' i‖ ≤ ‖c i‖) ∧
      ∀ a, ∑' i, c' i * e i a = 0 := by sorry
