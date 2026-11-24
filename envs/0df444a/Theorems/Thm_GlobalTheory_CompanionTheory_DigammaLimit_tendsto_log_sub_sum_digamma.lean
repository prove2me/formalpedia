-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DigammaLimit_tendsto_log_sub_sum_digamma
-- name    : GlobalTheory.CompanionTheory.DigammaLimit.tendsto_log_sub_sum_digamma
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:35:39.956636+00:00
-- url     : https://prove2.me/theorems/1422d3a9-d4d9-43f2-b98b-190f13f86d1f
-- title:
--   Digamma Limit: tendsto log sub sum digamma
-- statement:
--   The Digamma Limit construction uses the tendsto log sub sum digamma property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaTendstoLogSubHarmonic.lean#L164-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaTendstoLogSubHarmonic.lean#L164-L174

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

theorem GlobalTheory.CompanionTheory.DigammaLimit.tendsto_log_sub_sum_digamma : ∀ z : ℂ, 0 < z.re →
    Filter.Tendsto (fun n : ℕ => ((Real.log n : ℝ) : ℂ) -
      ∑ k ∈ Finset.range (n + 1), 1 / (z + (k : ℂ))) Filter.atTop (nhds (Complex.digamma z)) := by sorry
