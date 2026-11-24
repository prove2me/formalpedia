-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DigammaLimit_norm_GammaSeq_le
-- name    : GlobalTheory.CompanionTheory.DigammaLimit.norm_GammaSeq_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:35:34.009951+00:00
-- url     : https://prove2.me/theorems/0d90ac66-ff36-4cc6-b1b7-94e5bc08c53e
-- title:
--   Digamma Limit: norm Gamma Seq le
-- statement:
--   The Digamma Limit construction uses the norm Gamma Seq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaTendstoLogSubHarmonic.lean#L31-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaTendstoLogSubHarmonic.lean#L31-L41

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

theorem GlobalTheory.CompanionTheory.DigammaLimit.norm_GammaSeq_le {w : ℂ} (hw : 0 < w.re) {n : ℕ} (hn : n ≠ 0) :
    ‖GammaSeq w n‖ ≤ Real.Gamma w.re := by sorry
