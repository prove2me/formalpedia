-- Prove2me | Theorems.Thm_O3_Stage2RouteA_hasDerivAt_abs_affine_rpow
-- name    : O3.Stage2RouteA.hasDerivAt_abs_affine_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:31:33.552502+00:00
-- url     : https://prove2.me/theorems/2f070e16-c5f0-57f4-b321-b73087da8889
-- title:
--   Stage2 Route A: has Deriv At abs affine rpow
-- statement:
--   The Stage2 Route A construction uses the has Deriv At abs affine rpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteA.lean#L25-L32
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteA.lean#L25-L32

import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage2RouteA
set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteA

theorem O3.Stage2RouteA.hasDerivAt_abs_affine_rpow {p a b t : ℝ} (hp : 1 < p) :
    HasDerivAt (fun s : ℝ ↦ |a + s * b| ^ p)
      (p * |a + t * b| ^ (p - 2) * (a + t * b) * b) t := by sorry
