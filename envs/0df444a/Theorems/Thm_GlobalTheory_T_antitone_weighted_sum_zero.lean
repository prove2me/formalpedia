-- Prove2me | Theorems.Thm_GlobalTheory_T_antitone_weighted_sum_zero
-- name    : GlobalTheory.T.antitone_weighted_sum_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:26:20.813356+00:00
-- url     : https://prove2.me/theorems/7df7484a-4bb3-46bd-baba-162dac2f3b50
-- title:
--   T: antitone weighted sum zero
-- statement:
--   The T construction uses the antitone weighted sum zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AntitoneWeightedSumZeroStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AntitoneWeightedSumZeroStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AntitoneWeightedSumZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AntitoneWeightedSumZeroStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.antitone_weighted_sum_zero : ∀ (h : ℕ) (d e : Fin h → ℝ), (∀ i, 0 < d i) → Antitone e → ∑ i, d i * e i = 0 → (∀ j : Fin h, 0 ≤ ∑ i ∈ Finset.univ.filter (fun i => j ≤ i), d i * e i) → ∀ i, e i = 0 := by sorry
