-- Prove2me | Theorems.Thm_GlobalTheory_exponent_term
-- name    : GlobalTheory.exponent_term
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:22:01.085892+00:00
-- url     : https://prove2.me/theorems/53bf4937-692d-52aa-ba51-8c1db235b7e9
-- title:
--   Global Theory: exponent term
-- statement:
--   The Global Theory construction uses the exponent term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExponentDivisorSumLe.lean#L61-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExponentDivisorSumLe.lean#L61-L91

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

theorem GlobalTheory.exponent_term (k f r : ℕ) (G N H a Q l d : ℝ) (hk : 1 ≤ k)
    (hG : 1 ≤ G) (hN : 1 ≤ N) (hGH : G ≤ H) (hNH : N ≤ H) (ha : 0 ≤ a) (hQ : 0 ≤ Q)
    (hQH : Q * 9 ^ f ≤ H) (hl : 0 ≤ l) (hd : 1 ≤ d) (hdG : d ≤ G) :
    (d / N) ^ (k - 1) * a * (Q * H ^ (11 + 3 * l)) *
        ((G / d) ^ ((k : ℝ) + (1 + l) + 1) *
          (N ^ (2 * r) * G ^ r * 9 ^ f * H ^ (9 + 9 * r + 16 * r ^ 2))) ≤
      H ^ (24 + 4 * l + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2) * (a * (G / N) ^ k) := by sorry
