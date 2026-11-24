-- Prove2me | Theorems.Thm_GlobalTheory_fejer_re_ge
-- name    : GlobalTheory.fejer_re_ge
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:46:17.871443+00:00
-- url     : https://prove2.me/theorems/e2eb7690-0351-419e-8647-2576016314a4
-- title:
--   Global Theory: fejer re ge
-- statement:
--   The Global Theory construction uses the fejer re ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/WeightedFejerPositivity.lean#L51-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/WeightedFejerPositivity.lean#L51-L62

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

theorem GlobalTheory.fejer_re_ge (w : ℂ) (hw : ‖w‖ ≤ 1) (J : ℕ) :
    -(1 / 2) ≤ ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (w ^ j).re := by sorry
