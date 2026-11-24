-- Prove2me | Theorems.Thm_GroundTheory_Global_Quadratic_hasDerivAt_add_cpow
-- name    : GroundTheory.Global.Quadratic.hasDerivAt_add_cpow
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:39:16.781851+00:00
-- url     : https://prove2.me/theorems/1f2c9693-3ade-4dc4-945c-f3219cf414b9
-- title:
--   Quadratic: has Deriv At add cpow
-- statement:
--   The Quadratic construction uses the has Deriv At add cpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/AnalyticClassNumber/QuadraticHurwitzZero.lean#L10-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/AnalyticClassNumber/QuadraticHurwitzZero.lean#L10-L22

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

theorem GroundTheory.Global.Quadratic.hasDerivAt_add_cpow (n : ℕ) {t : ℝ} (ht : 0 < (n : ℝ) + t) (c : ℂ) :
    HasDerivAt (fun u : ℝ ↦ (((n : ℝ) + u : ℝ) : ℂ) ^ c)
      (c * (((n : ℝ) + t : ℝ) : ℂ) ^ (c - 1)) t := by sorry
