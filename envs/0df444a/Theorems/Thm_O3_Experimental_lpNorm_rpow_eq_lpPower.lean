-- Prove2me | Theorems.Thm_O3_Experimental_lpNorm_rpow_eq_lpPower
-- name    : O3.Experimental.lpNorm_rpow_eq_lpPower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:55:07.250021+00:00
-- url     : https://prove2.me/theorems/58a6e4d5-c6ae-40c6-81e8-687c308ad5cf
-- title:
--   Experimental: lp Norm rpow eq lp Power
-- statement:
--   The Experimental construction uses the lp Norm rpow eq lp Power property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/GeometryExperimental.lean#L223-L227
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/GeometryExperimental.lean#L223-L227

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_GeometryExperimental
set_option autoImplicit true
open O3 O3.Experimental

theorem O3.Experimental.lpNorm_rpow_eq_lpPower {p : ℝ} (hp : p ≠ 0) {d : ℕ} (z : Point d) :
    (lpNorm p z) ^ p = lpPower p z := by sorry
