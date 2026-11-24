-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DigammaLimit_tendsto_deriv_GammaSeq
-- name    : GlobalTheory.CompanionTheory.DigammaLimit.tendsto_deriv_GammaSeq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:35:32.250801+00:00
-- url     : https://prove2.me/theorems/e3b3735a-5457-48d2-a01c-043d66be6f74
-- title:
--   Digamma Limit: tendsto deriv Gamma Seq
-- statement:
--   The Digamma Limit construction uses the tendsto deriv Gamma Seq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaTendstoLogSubHarmonic.lean#L93-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaTendstoLogSubHarmonic.lean#L93-L162

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

theorem GlobalTheory.CompanionTheory.DigammaLimit.tendsto_deriv_GammaSeq {z : ℂ} (hz : 0 < z.re) :
    Tendsto (fun n : ℕ => deriv (fun w => GammaSeq w n) z) atTop (𝓝 (deriv Gamma z)) := by sorry
