-- Prove2me | Theorems.Thm_GlobalTheory_normSq_geomSum_le_fejer
-- name    : GlobalTheory.normSq_geomSum_le_fejer
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:12:20.566234+00:00
-- url     : https://prove2.me/theorems/46bb12fe-c267-454d-81e2-5016ef24320d
-- title:
--   Global Theory: norm Sq geom Sum le fejer
-- statement:
--   The Global Theory construction uses the norm Sq geom Sum le fejer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/WeightedFejerPositivity.lean#L6-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/WeightedFejerPositivity.lean#L6-L49

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

theorem GlobalTheory.normSq_geomSum_le_fejer (w : ℂ) (hw : ‖w‖ ≤ 1) (J : ℕ) :
    Complex.normSq (∑ j ∈ Finset.range (J + 1), w ^ j) ≤
      (J + 1 : ℝ) + 2 * ∑ j ∈ Finset.Icc 1 J, ((J : ℝ) + 1 - j) * (w ^ j).re := by sorry
