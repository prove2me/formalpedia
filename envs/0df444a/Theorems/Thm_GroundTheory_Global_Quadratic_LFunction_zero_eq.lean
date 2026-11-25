-- Prove2me | Theorems.Thm_GroundTheory_Global_Quadratic_LFunction_zero_eq
-- name    : GroundTheory.Global.Quadratic.LFunction_zero_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:39:37.615437+00:00
-- url     : https://prove2.me/theorems/6bb67cca-cb3c-4113-a311-157e08e62ff9
-- title:
--   Quadratic: LFunction zero eq
-- statement:
--   The Quadratic construction uses the LFunction zero eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/AnalyticClassNumber/QuadraticHurwitzZero.lean#L277-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/AnalyticClassNumber/QuadraticHurwitzZero.lean#L277-L299

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

theorem GroundTheory.Global.Quadratic.LFunction_zero_eq {N : ℕ} [NeZero N] {Φ : ZMod N → ℂ} (h0 : Φ 0 = 0)
    (hsum : ∑ j, Φ j = 0) :
    ZMod.LFunction Φ 0 = -(1 / N) * ∑ j : ZMod N, Φ j * (j.val : ℂ) := by sorry
