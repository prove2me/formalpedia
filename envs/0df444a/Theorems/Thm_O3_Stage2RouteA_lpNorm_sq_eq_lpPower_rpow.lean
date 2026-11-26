-- Prove2me | Theorems.Thm_O3_Stage2RouteA_lpNorm_sq_eq_lpPower_rpow
-- name    : O3.Stage2RouteA.lpNorm_sq_eq_lpPower_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:31:11.276357+00:00
-- url     : https://prove2.me/theorems/954c4deb-724d-5957-9e72-3d97193fad92
-- title:
--   Stage2 Route A: lp Norm sq eq lp Power rpow
-- statement:
--   The squared norm written as a single real power of the finite power sum.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteA.lean#L49-L55
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteA.lean#L49-L55

import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage2RouteA
set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteA

theorem O3.Stage2RouteA.lpNorm_sq_eq_lpPower_rpow {p : ℝ} (hp : p ≠ 0) {d : ℕ} (z : Point d) :
    (lpNorm p z) ^ (2 : ℕ) = (lpPower p z) ^ (2 / p) := by sorry
