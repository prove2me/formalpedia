-- Prove2me | Theorems.Thm_O3_lpNorm_two_sq_eq_pairing
-- name    : O3.lpNorm_two_sq_eq_pairing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:25:01.557505+00:00
-- url     : https://prove2.me/theorems/3630e6fb-42ce-5c76-beed-2a03ad5bf7b8
-- title:
--   O3: lp Norm two sq eq pairing
-- statement:
--   Literal `lpNorm 2` squared is the coordinate pairing with itself.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage9Telescoping.lean#L139-L145
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage9Telescoping.lean#L139-L145

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage9Telescoping
set_option autoImplicit true
open scoped BigOperators
open O3

theorem O3.lpNorm_two_sq_eq_pairing {d : ℕ} (x : Vec d) :
    (lpNorm 2 x) ^ (2 : ℕ) = pairing x x := by sorry
