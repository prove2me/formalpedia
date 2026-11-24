-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DigammaLimit_euler_seq_le_Gamma
-- name    : GlobalTheory.CompanionTheory.DigammaLimit.euler_seq_le_Gamma
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:35:16.443398+00:00
-- url     : https://prove2.me/theorems/0e1c6c98-97ed-4d54-8993-3f9c2058572a
-- title:
--   Digamma Limit: euler seq le Gamma
-- statement:
--   The Digamma Limit construction uses the euler seq le Gamma property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaTendstoLogSubHarmonic.lean#L8-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaTendstoLogSubHarmonic.lean#L8-L29

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

theorem GlobalTheory.CompanionTheory.DigammaLimit.euler_seq_le_Gamma {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : n ≠ 0) :
    (n : ℝ) ^ x * (n ! : ℝ) / ∏ j ∈ Finset.range (n + 1), (x + (j : ℝ)) ≤ Real.Gamma x := by sorry
