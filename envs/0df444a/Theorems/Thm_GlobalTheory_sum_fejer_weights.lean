-- Prove2me | Theorems.Thm_GlobalTheory_sum_fejer_weights
-- name    : GlobalTheory.sum_fejer_weights
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:23:09.269189+00:00
-- url     : https://prove2.me/theorems/2c064429-a9f5-49b8-a788-1aba8cda0fc6
-- title:
--   Global Theory: sum fejer weights
-- statement:
--   The Global Theory construction uses the sum fejer weights property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/WeightedFejerPositivity.lean#L64-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/WeightedFejerPositivity.lean#L64-L77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_WeightedFejerPositivity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory

theorem GlobalTheory.sum_fejer_weights (J : ℕ) :
    ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) = (J : ℝ) / 2 := by sorry
