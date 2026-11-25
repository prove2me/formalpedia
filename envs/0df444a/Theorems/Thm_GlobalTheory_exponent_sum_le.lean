-- Prove2me | Theorems.Thm_GlobalTheory_exponent_sum_le
-- name    : GlobalTheory.exponent_sum_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:22:22.954375+00:00
-- url     : https://prove2.me/theorems/d1a635ec-266e-440d-aace-b682cd2ddb94
-- title:
--   Global Theory: exponent sum le
-- statement:
--   The Global Theory construction uses the exponent sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExponentDivisorSumLe.lean#L93-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExponentDivisorSumLe.lean#L93-L138

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExponentDivisorSumLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open GlobalTheory

theorem GlobalTheory.exponent_sum_le :
    ∀ (k f r : ℕ) (G N H a Q C : ℝ), 1 ≤ k → 1 ≤ r → 1 ≤ f → Real.log f ≤ Real.sqrt r → 1 ≤ G → 1 ≤ N → G ≤ H → N ≤ H → 0 ≤ a → 0 ≤ Q → Q * 9 ^ f ≤ H → 60 ≤ C → ∑ de ∈ Finset.Icc 1 ⌊G⌋₊, ((de : ℝ) / N) ^ (k - 1) * a * (Q * H ^ (11 + 3 * Real.logb 2 f)) * ((G / de) ^ ((k : ℝ) + Real.logb 2 (2 * f) + 1) * (N ^ (2 * r) * G ^ r * 9 ^ f * H ^ (9 + 9 * r + 16 * r ^ 2))) ≤ H ^ (C * (r : ℝ) ^ 2) * (a * (G / N) ^ k) := by sorry
