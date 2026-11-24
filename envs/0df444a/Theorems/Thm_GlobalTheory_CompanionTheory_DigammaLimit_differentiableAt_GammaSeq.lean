-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DigammaLimit_differentiableAt_GammaSeq
-- name    : GlobalTheory.CompanionTheory.DigammaLimit.differentiableAt_GammaSeq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:35:06.009276+00:00
-- url     : https://prove2.me/theorems/573f4460-4796-473c-9bc0-181f3629bec7
-- title:
--   Digamma Limit: differentiable At Gamma Seq
-- statement:
--   The Digamma Limit construction uses the differentiable At Gamma Seq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaTendstoLogSubHarmonic.lean#L54-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaTendstoLogSubHarmonic.lean#L54-L61

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

theorem GlobalTheory.CompanionTheory.DigammaLimit.differentiableAt_GammaSeq {z : ℂ} (hz : 0 < z.re) {n : ℕ} (hn : n ≠ 0) :
    DifferentiableAt ℂ (fun w => GammaSeq w n) z := by sorry
