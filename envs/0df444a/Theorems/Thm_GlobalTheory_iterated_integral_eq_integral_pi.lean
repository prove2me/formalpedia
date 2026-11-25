-- Prove2me | Theorems.Thm_GlobalTheory_iterated_integral_eq_integral_pi
-- name    : GlobalTheory.iterated_integral_eq_integral_pi
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:48:46.67883+00:00
-- url     : https://prove2.me/theorems/e1aac411-d0a6-4572-9dd9-cdfe95345f18
-- title:
--   Global Theory: iterated integral eq integral pi
-- statement:
--   The Global Theory construction uses the iterated integral eq integral pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/MeasurePreservingSnocMeasurableEquiv.lean#L31-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/MeasurePreservingSnocMeasurableEquiv.lean#L31-L101

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MeasurePreservingSnocMeasurableEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open GlobalTheory

theorem GlobalTheory.iterated_integral_eq_integral_pi :
    ∀ (n : ℕ) (W : ℕ → ℂ → ℝ) (R : (j : ℕ) → (Fin j → ℂ) → ℝ), (∀ j t, 0 ≤ W j t) → (∀ c : Fin n → ℂ, (∀ i, c i ≠ 0) → 0 ≤ R n c) → AEMeasurable (fun c : Fin n → ℂ => (∏ i : Fin n, W ((i : ℕ) + 1) (c i)) * R n c) → (∀ j, j < n → ∀ c : Fin j → ℂ, (∀ i, c i ≠ 0) → Integrable (fun t : ℂ => W (j + 1) t * R (j + 1) (Fin.snoc c t)) ∧ R j c = ∫ t : ℂ, W (j + 1) t * R (j + 1) (Fin.snoc c t)) → Integrable (fun c : Fin n → ℂ => (∏ i : Fin n, W ((i : ℕ) + 1) (c i)) * R n c) ∧ R 0 (fun i => i.elim0) = ∫ c : Fin n → ℂ, (∏ i : Fin n, W ((i : ℕ) + 1) (c i)) * R n c := by sorry
