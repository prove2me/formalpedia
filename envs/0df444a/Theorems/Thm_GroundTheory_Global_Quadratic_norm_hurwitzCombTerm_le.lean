-- Prove2me | Theorems.Thm_GroundTheory_Global_Quadratic_norm_hurwitzCombTerm_le
-- name    : GroundTheory.Global.Quadratic.norm_hurwitzCombTerm_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:39:15.494223+00:00
-- url     : https://prove2.me/theorems/b17f9510-8c5d-4246-8f39-b4145e54d619
-- title:
--   Quadratic: norm hurwitz Comb Term le
-- statement:
--   The Quadratic construction uses the norm hurwitz Comb Term le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/AnalyticClassNumber/QuadraticHurwitzZero.lean#L126-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/AnalyticClassNumber/QuadraticHurwitzZero.lean#L126-L199

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

theorem GroundTheory.Global.Quadratic.norm_hurwitzCombTerm_le {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (n : ℕ) {s : ℂ}
    (hs : s ∈ Metric.ball (1 : ℂ) (3 / 2)) :
    ‖hurwitzCombTerm x n s‖ ≤
      18 * (((n : ℝ) + min x (1 / 2)) ^ (-(3 / 2) : ℝ) + ((n : ℝ) + min x (1 / 2)) ^ (-(9 / 2) : ℝ)) := by sorry
