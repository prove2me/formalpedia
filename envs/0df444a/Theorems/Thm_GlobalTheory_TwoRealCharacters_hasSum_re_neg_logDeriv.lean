-- Prove2me | Theorems.Thm_GlobalTheory_TwoRealCharacters_hasSum_re_neg_logDeriv
-- name    : GlobalTheory.TwoRealCharacters.hasSum_re_neg_logDeriv
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:15:39.880952+00:00
-- url     : https://prove2.me/theorems/83fef204-9987-442b-845d-92505dbf50a9
-- title:
--   Two Real Characters: has Sum re neg log Deriv
-- statement:
--   The Two Real Characters construction uses the has Sum re neg log Deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NegSumLogDerivNonneg.lean#L7-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NegSumLogDerivNonneg.lean#L7-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NegSumLogDerivNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.TwoRealCharacters

theorem GlobalTheory.TwoRealCharacters.hasSum_re_neg_logDeriv (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (σ : ℝ)
    (hσ : 1 < σ) :
    HasSum (fun n : ℕ => (χ n).re * (vonMangoldt n / (n : ℝ) ^ σ))
      (-(deriv (LFunction χ) σ / LFunction χ σ).re) := by sorry
