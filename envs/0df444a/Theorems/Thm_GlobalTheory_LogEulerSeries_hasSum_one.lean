-- Prove2me | Theorems.Thm_GlobalTheory_LogEulerSeries_hasSum_one
-- name    : GlobalTheory.LogEulerSeries.hasSum_one
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:18:54.811791+00:00
-- url     : https://prove2.me/theorems/9923e0d4-af16-4bb7-9216-203858739f89
-- title:
--   Log Euler Series: has Sum one
-- statement:
--   The Log Euler Series construction uses the has Sum one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/HasSumLogZetaSqMul.lean#L37-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/HasSumLogZetaSqMul.lean#L37-L61

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

theorem GlobalTheory.LogEulerSeries.hasSum_one {ι : Type} (N : ι → ℕ) (c : ι → ℂ) (hN : ∀ i, 2 ≤ N i) (hc : ∀ i, ‖c i‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) (hsum : Summable fun i => (N i : ℝ) ^ (-s.re)) :
    HasSum (fun p : ι × ℕ => c p.1 ^ (p.2 + 1) / ((p.2 : ℂ) + 1) *
        Complex.exp (-((((p.2 : ℝ) + 1) * Real.log (N p.1) : ℝ) : ℂ) * s))
      (∑' i, -Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))) := by sorry
