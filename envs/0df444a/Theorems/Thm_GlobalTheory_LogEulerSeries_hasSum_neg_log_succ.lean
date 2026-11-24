-- Prove2me | Theorems.Thm_GlobalTheory_LogEulerSeries_hasSum_neg_log_succ
-- name    : GlobalTheory.LogEulerSeries.hasSum_neg_log_succ
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:18:52.631795+00:00
-- url     : https://prove2.me/theorems/6825e117-11a9-48a9-a3fd-3d4c8ffea58b
-- title:
--   Log Euler Series: has Sum neg log succ
-- statement:
--   The Log Euler Series construction uses the has Sum neg log succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/HasSumLogZetaSqMul.lean#L8-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/HasSumLogZetaSqMul.lean#L8-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HasSumLogZetaSqMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open GlobalTheory GlobalTheory.LogEulerSeries

theorem GlobalTheory.LogEulerSeries.hasSum_neg_log_succ {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => z ^ (k + 1) / ((k : ℂ) + 1)) (-Complex.log (1 - z)) := by sorry
