-- Prove2me | Theorems.Thm_GlobalTheory_Harm_casimir_value_strict
-- name    : GlobalTheory.Harm.casimir_value_strict
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:07:08.04626+00:00
-- url     : https://prove2.me/theorems/bccc1933-a5dd-46ae-85c2-9323b81bd3a0
-- title:
--   Harm: casimir value strict
-- statement:
--   The Harm construction uses the casimir value strict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/EqZeroOfPartialSumsNonneg.lean#L36-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/EqZeroOfPartialSumsNonneg.lean#L36-L102

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_EqZeroOfPartialSumsNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Harm
open Finset
open Finset

theorem GlobalTheory.Harm.casimir_value_strict {m : ℕ} (κ κ₀ : Fin m → ℤ) (h : Antitone κ)
    (h₀ : Antitone κ₀)
    (hle : ∀ i : ℕ, ∑ k ∈ Finset.univ.filter (fun k : Fin m => (k : ℕ) < i), κ k ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin m => (k : ℕ) < i), κ₀ k)
    (hsum : ∑ k, κ k = ∑ k, κ₀ k)
    (hC : ∑ i, κ₀ i * (κ₀ i + m - 1 - 2 * (i : ℕ)) ≤ ∑ i, κ i * (κ i + m - 1 - 2 * (i : ℕ))) : κ = κ₀ := by sorry
