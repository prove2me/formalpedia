-- Prove2me | Theorems.Thm_GlobalTheory_entire_exists_polynomial_of_poly_bound
-- name    : GlobalTheory.entire_exists_polynomial_of_poly_bound
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:17:25.895563+00:00
-- url     : https://prove2.me/theorems/9167ea84-ee6e-4ec0-8b11-9b4c683a5073
-- title:
--   Global Theory: entire exists polynomial of poly bound
-- statement:
--   The Global Theory construction uses the entire exists polynomial of poly bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EntireApplyEqOfPeriodicOfSpanReal.lean#L126-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EntireApplyEqOfPeriodicOfSpanReal.lean#L126-L135

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Metric Filter Topology
open scoped Nat
open GlobalTheory
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

theorem GlobalTheory.entire_exists_polynomial_of_poly_bound {F : ℂ → ℂ} (hF : Differentiable ℂ F) {C : ℝ}
    {m : ℕ} (hb : ∀ z, ‖F z‖ ≤ C * (1 + ‖z‖) ^ m) :
    ∃ p : Polynomial ℂ, p.natDegree ≤ m ∧ ∀ z, F z = p.eval z := by sorry
