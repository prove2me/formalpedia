-- Prove2me | Theorems.Thm_O3_Stage2RouteA_hasDerivAt_scalarJ_of_ne_zero
-- name    : O3.Stage2RouteA.hasDerivAt_scalarJ_of_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:32:17.446944+00:00
-- url     : https://prove2.me/theorems/178555a9-0af7-494d-bb96-fe45a69bc3bc
-- title:
--   Stage2 Route A: has Deriv At scalar J of ne zero
-- statement:
--   Away from the scalar singularity, the derivative of
--   `|u|^(p-2)u` has its expected exact coefficient.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteA.lean#L114-L158
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteA.lean#L114-L158

import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage2RouteA
set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteA

theorem O3.Stage2RouteA.hasDerivAt_scalarJ_of_ne_zero {p u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (O3.Experimental.scalarJ p) ((p - 1) * |u| ^ (p - 2)) u := by sorry
