-- Prove2me | Theorems.Thm_O3_Stage2RouteA_lpPower_rpow_two_div_sub_one_eq
-- name    : O3.Stage2RouteA.lpPower_rpow_two_div_sub_one_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:31:19.85181+00:00
-- url     : https://prove2.me/theorems/9eab6cde-8e39-511d-aa8d-e1abfab74c64
-- title:
--   Stage2 Route A: lp Power rpow two div sub one eq
-- statement:
--   The Stage2 Route A construction uses the lp Power rpow two div sub one eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteA.lean#L67-L74
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteA.lean#L67-L74

import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage2RouteA
set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteA

theorem O3.Stage2RouteA.lpPower_rpow_two_div_sub_one_eq {p : ℝ} (hp : p ≠ 0) {d : ℕ}
    {z : Point d} (hz : z ≠ 0) :
    (lpPower p z) ^ (2 / p - 1) = (lpNorm p z) ^ (2 - p) := by sorry
