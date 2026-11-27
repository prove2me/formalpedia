-- Prove2me | Theorems.Thm_GroundTheory_Global_Quadratic_LFunction_zero_eq_of_ne_one
-- name    : GroundTheory.Global.Quadratic.LFunction_zero_eq_of_ne_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:54:44.967521+00:00
-- url     : https://prove2.me/theorems/fb27bebf-b816-5edc-8057-39a36cf9f4df
-- title:
--   Quadratic: LFunction zero eq of ne one
-- statement:
--   The Quadratic construction uses the LFunction zero eq of ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/AnalyticClassNumber/QuadraticHurwitzZero.lean#L301-L307
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/AnalyticClassNumber/QuadraticHurwitzZero.lean#L301-L307

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

theorem GroundTheory.Global.Quadratic.LFunction_zero_eq_of_ne_one {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    DirichletCharacter.LFunction χ 0 = -(1 / N) * ∑ a : ZMod N, χ a * (a.val : ℂ) := by sorry
