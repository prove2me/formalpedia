-- Prove2me | Theorems.Thm_O3_stage9P_gradient_eq
-- name    : O3.stage9P_gradient_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:25:02.88084+00:00
-- url     : https://prove2.me/theorems/e80123ea-3040-5dc2-a47c-dd419b112bf9
-- title:
--   O3: stage9 P gradient eq
-- statement:
--   Rearranged auxiliary recurrence, with every division justified.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage9Telescoping.lean#L121-L129
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage9Telescoping.lean#L121-L129

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage9Telescoping
set_option autoImplicit true
open scoped BigOperators
open O3

theorem O3.stage9P_gradient_eq {d : ℕ} {theta : ℕ → ℝ} {g : ℕ → Vec d}
    {k : ℕ} (hθ : theta k ≠ 0) :
    g k = theta k • stage9P theta g (k + 1) -
      (theta k - 1) • stage9P theta g k := by sorry
