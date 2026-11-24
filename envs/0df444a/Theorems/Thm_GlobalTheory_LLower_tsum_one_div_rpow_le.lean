-- Prove2me | Theorems.Thm_GlobalTheory_LLower_tsum_one_div_rpow_le
-- name    : GlobalTheory.LLower.tsum_one_div_rpow_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:56:01.907799+00:00
-- url     : https://prove2.me/theorems/a97b5a44-f236-42b9-b281-5e16c6810299
-- title:
--   LLower: tsum one div rpow le
-- statement:
--   The LLower construction uses the tsum one div rpow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TsumOneDivRpowLe.lean#L6-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TsumOneDivRpowLe.lean#L6-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TsumOneDivRpowLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.LLower

theorem GlobalTheory.LLower.tsum_one_div_rpow_le {σ : ℝ} (hσ : 1 < σ) :
    ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ σ ≤ σ / (σ - 1) := by sorry
