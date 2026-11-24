-- Prove2me | Theorems.Thm_GlobalTheory_LogEulerSeries_hasSum_prod_neg_log
-- name    : GlobalTheory.LogEulerSeries.hasSum_prod_neg_log
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:19:07.485972+00:00
-- url     : https://prove2.me/theorems/efc7e472-2a89-4abb-92d2-bece3bde8cdf
-- title:
--   Log Euler Series: has Sum prod neg log
-- statement:
--   The Log Euler Series construction uses the has Sum prod neg log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/HasSumLogZetaSqMul.lean#L14-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/HasSumLogZetaSqMul.lean#L14-L35

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

theorem GlobalTheory.LogEulerSeries.hasSum_prod_neg_log {ι : Type} (z : ι → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1 / 2)
    (hs : Summable fun i => ‖z i‖) :
    HasSum (fun p : ι × ℕ => z p.1 ^ (p.2 + 1) / ((p.2 : ℂ) + 1))
      (∑' i, -Complex.log (1 - z i)) := by sorry
