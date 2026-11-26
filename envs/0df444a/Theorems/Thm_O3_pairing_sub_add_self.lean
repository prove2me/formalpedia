-- Prove2me | Theorems.Thm_O3_pairing_sub_add_self
-- name    : O3.pairing_sub_add_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:25:10.597218+00:00
-- url     : https://prove2.me/theorems/3d534e2e-9c59-43c5-9d77-f288d53c9d09
-- title:
--   O3: pairing sub add self
-- statement:
--   Exact Euclidean polarization, still in the project's literal norm.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage9Telescoping.lean#L148-L157
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage9Telescoping.lean#L148-L157

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage9Telescoping
set_option autoImplicit true
open scoped BigOperators
open O3

theorem O3.pairing_sub_add_self {d : ℕ} (x y : Vec d) :
    pairing (x - y) (x + y) =
      (lpNorm 2 x) ^ (2 : ℕ) - (lpNorm 2 y) ^ (2 : ℕ) := by sorry
