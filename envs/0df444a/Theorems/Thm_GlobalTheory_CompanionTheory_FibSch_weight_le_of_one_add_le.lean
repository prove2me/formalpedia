-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FibSch_weight_le_of_one_add_le
-- name    : GlobalTheory.CompanionTheory.FibSch.weight_le_of_one_add_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:39:57.694797+00:00
-- url     : https://prove2.me/theorems/98b5474c-20c9-412a-b3c5-7afb49f8e1e4
-- title:
--   Fib Sch: weight le of one add le
-- statement:
--   The Fib Sch construction uses the weight le of one add le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LintegralUniformNearParameter.lean#L7-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LintegralUniformNearParameter.lean#L7-L15

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LintegralUniformNearParameter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FibSch

theorem GlobalTheory.CompanionTheory.FibSch.weight_le_of_one_add_le {a b M : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ)
    (h : 1 + a ≤ M * (1 + b)) :
    (1 + b) ^ (-(n : ℝ)) ≤ M ^ n * (1 + a) ^ (-(n : ℝ)) := by sorry
