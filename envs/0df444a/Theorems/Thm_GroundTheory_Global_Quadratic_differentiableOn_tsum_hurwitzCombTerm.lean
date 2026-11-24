-- Prove2me | Theorems.Thm_GroundTheory_Global_Quadratic_differentiableOn_tsum_hurwitzCombTerm
-- name    : GroundTheory.Global.Quadratic.differentiableOn_tsum_hurwitzCombTerm
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:39:45.573419+00:00
-- url     : https://prove2.me/theorems/68624577-7a8a-4cc2-8bcf-1ccb43ce06cb
-- title:
--   Quadratic: differentiable On tsum hurwitz Comb Term
-- statement:
--   The Quadratic construction uses the differentiable On tsum hurwitz Comb Term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/AnalyticClassNumber/QuadraticHurwitzZero.lean#L210-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/AnalyticClassNumber/QuadraticHurwitzZero.lean#L210-L220

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

theorem GroundTheory.Global.Quadratic.differentiableOn_tsum_hurwitzCombTerm {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    DifferentiableOn ℂ (fun s ↦ ∑' n, hurwitzCombTerm x n s) (Metric.ball 1 (3 / 2)) := by sorry
