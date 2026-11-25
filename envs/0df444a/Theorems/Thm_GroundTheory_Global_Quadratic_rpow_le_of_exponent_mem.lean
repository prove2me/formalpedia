-- Prove2me | Theorems.Thm_GroundTheory_Global_Quadratic_rpow_le_of_exponent_mem
-- name    : GroundTheory.Global.Quadratic.rpow_le_of_exponent_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:39:30.475301+00:00
-- url     : https://prove2.me/theorems/80466e3b-02ea-4ab2-ad2c-718786a86d0e
-- title:
--   Quadratic: rpow le of exponent mem
-- statement:
--   The Quadratic construction uses the rpow le of exponent mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/AnalyticClassNumber/QuadraticHurwitzZero.lean#L69-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/AnalyticClassNumber/QuadraticHurwitzZero.lean#L69-L80

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

theorem GroundTheory.Global.Quadratic.rpow_le_of_exponent_mem {b c e : ℝ} (hc : 0 < c) (hcb : c ≤ b) (he1 : -(9 / 2) ≤ e)
    (he2 : e ≤ -(3 / 2)) : b ^ e ≤ c ^ (-(3 / 2) : ℝ) + c ^ (-(9 / 2) : ℝ) := by sorry
