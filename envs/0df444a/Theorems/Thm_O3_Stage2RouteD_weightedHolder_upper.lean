-- Prove2me | Theorems.Thm_O3_Stage2RouteD_weightedHolder_upper
-- name    : O3.Stage2RouteD.weightedHolder_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:12:01.659396+00:00
-- url     : https://prove2.me/theorems/91f3b302-c42f-51f5-8e81-2f5487883301
-- title:
--   Stage2 Route D: weighted Holder upper
-- statement:
--   The exact weighted Holder estimate in the nonsingular `q > 2` Hessian.
--   This is the analytic core of the conjugate-smoothness route.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteD.lean#L133-L162
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteD.lean#L133-L162

import Definitions.Def_O3_GeometryExperimental
import Definitions.Def_O3_Stage2RouteD
set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteD

theorem O3.Stage2RouteD.weightedHolder_upper {q : ℝ} (hq : 2 < q) {d : ℕ}
    (z h : Point d) (hz : z ≠ 0) :
    (lpNorm q z) ^ (2 - q) *
        (∑ i, |z i| ^ (q - 2) * (h i) ^ (2 : ℕ)) ≤
      (lpNorm q h) ^ (2 : ℕ) := by sorry
