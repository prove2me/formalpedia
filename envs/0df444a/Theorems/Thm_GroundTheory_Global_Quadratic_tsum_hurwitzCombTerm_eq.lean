-- Prove2me | Theorems.Thm_GroundTheory_Global_Quadratic_tsum_hurwitzCombTerm_eq
-- name    : GroundTheory.Global.Quadratic.tsum_hurwitzCombTerm_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:39:28.661991+00:00
-- url     : https://prove2.me/theorems/c0db4a00-0cc0-4f96-94fd-c169490e85ec
-- title:
--   Quadratic: tsum hurwitz Comb Term eq
-- statement:
--   The Quadratic construction uses the tsum hurwitz Comb Term eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/AnalyticClassNumber/QuadraticHurwitzZero.lean#L222-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/AnalyticClassNumber/QuadraticHurwitzZero.lean#L222-L236

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

theorem GroundTheory.Global.Quadratic.tsum_hurwitzCombTerm_eq {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) {s : ℂ}
    (hs : s ∈ Metric.ball (1 : ℂ) (3 / 2)) :
    ∑' n, hurwitzCombTerm x n s = hurwitzComb x s := by sorry
