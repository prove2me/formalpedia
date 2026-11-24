-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DigammaLimit_logDeriv_GammaSeq
-- name    : GlobalTheory.CompanionTheory.DigammaLimit.logDeriv_GammaSeq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:35:24.548803+00:00
-- url     : https://prove2.me/theorems/caf2a2c5-2abc-4ef7-9826-44048df2d10c
-- title:
--   Digamma Limit: log Deriv Gamma Seq
-- statement:
--   The Digamma Limit construction uses the log Deriv Gamma Seq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaTendstoLogSubHarmonic.lean#L63-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaTendstoLogSubHarmonic.lean#L63-L91

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaTendstoLogSubHarmonic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Metric Set
open scoped Nat Real
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DigammaLimit

theorem GlobalTheory.CompanionTheory.DigammaLimit.logDeriv_GammaSeq {z : ℂ} (hz : 0 < z.re) {n : ℕ} (hn : n ≠ 0) :
    logDeriv (fun w => GammaSeq w n) z =
      ((Real.log n : ℝ) : ℂ) - ∑ k ∈ Finset.range (n + 1), 1 / (z + (k : ℂ)) := by sorry
