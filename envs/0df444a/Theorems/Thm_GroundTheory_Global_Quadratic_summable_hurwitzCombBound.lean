-- Prove2me | Theorems.Thm_GroundTheory_Global_Quadratic_summable_hurwitzCombBound
-- name    : GroundTheory.Global.Quadratic.summable_hurwitzCombBound
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:39:30.784464+00:00
-- url     : https://prove2.me/theorems/97cdec32-7904-4ef5-8e8a-7eea83842fa8
-- title:
--   Quadratic: summable hurwitz Comb Bound
-- statement:
--   The Quadratic construction uses the summable hurwitz Comb Bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/AnalyticClassNumber/QuadraticHurwitzZero.lean#L201-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/AnalyticClassNumber/QuadraticHurwitzZero.lean#L201-L208

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_AnalyticClassNumber_QuadraticHurwitzZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open Complex HurwitzZeta Filter Topology Set
open GroundTheory GroundTheory.Global GroundTheory.Global.Quadratic

theorem GroundTheory.Global.Quadratic.summable_hurwitzCombBound {x₀ : ℝ} (hx₀ : 0 < x₀) :
    Summable (fun n : ℕ ↦ 18 * (((n : ℝ) + x₀) ^ (-(3 / 2) : ℝ) + ((n : ℝ) + x₀) ^ (-(9 / 2) : ℝ))) := by sorry
