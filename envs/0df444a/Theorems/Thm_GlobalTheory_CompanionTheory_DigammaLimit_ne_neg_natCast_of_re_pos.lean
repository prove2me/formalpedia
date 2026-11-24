-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DigammaLimit_ne_neg_natCast_of_re_pos
-- name    : GlobalTheory.CompanionTheory.DigammaLimit.ne_neg_natCast_of_re_pos
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:35:16.196842+00:00
-- url     : https://prove2.me/theorems/83705799-d0a1-4174-be97-c585bcdabf6c
-- title:
--   Digamma Limit: ne neg nat Cast of re pos
-- statement:
--   The Digamma Limit construction uses the ne neg nat Cast of re pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaTendstoLogSubHarmonic.lean#L50-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaTendstoLogSubHarmonic.lean#L50-L52

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

theorem GlobalTheory.CompanionTheory.DigammaLimit.ne_neg_natCast_of_re_pos {z : ℂ} (hz : 0 < z.re) (m : ℕ) : z ≠ -(m : ℂ) := by sorry
