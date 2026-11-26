-- Prove2me | Theorems.Thm_O3_Stage2RouteA_hasDerivAt_scalarJ_affine
-- name    : O3.Stage2RouteA.hasDerivAt_scalarJ_affine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:31:52.47369+00:00
-- url     : https://prove2.me/theorems/085d159d-774a-5acf-879a-450e585bc6eb
-- title:
--   Stage2 Route A: has Deriv At scalar J affine
-- statement:
--   The Stage2 Route A construction uses the has Deriv At scalar J affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteA.lean#L200-L209
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteA.lean#L200-L209

import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage2RouteA
set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteA

theorem O3.Stage2RouteA.hasDerivAt_scalarJ_affine {p a b t : ℝ} (hz : a + t * b ≠ 0) :
    HasDerivAt (fun s : ℝ ↦ O3.Experimental.scalarJ p (a + s * b))
      ((p - 1) * |a + t * b| ^ (p - 2) * b) t := by sorry
