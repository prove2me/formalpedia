-- Prove2me | Theorems.Thm_O3_Stage2RouteB_deriv_squaredLpEnergy_line
-- name    : O3.Stage2RouteB.deriv_squaredLpEnergy_line
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:21:52.601984+00:00
-- url     : https://prove2.me/theorems/d24b6ab6-8137-5298-b02d-05c0b7e81274
-- title:
--   Stage2 Route B: deriv squared Lp Energy line
-- statement:
--   The explicit finite-dimensional squared `ell_p` energy has normalized
--   duality-map directional derivative everywhere, including zero coordinates and
--   the origin.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteB.lean#L238-L244
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteB.lean#L238-L244

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_Stage2RouteB
set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteB

theorem O3.Stage2RouteB.deriv_squaredLpEnergy_line {p : ℝ} (hp : 1 < p) {d : ℕ}
    (x h : Point d) (t : ℝ) :
    deriv (fun s : ℝ ↦ squaredLpEnergy p (fun i ↦ x i + s * h i)) t =
      pairing (dualityMap p (fun i ↦ x i + t * h i)) h := by sorry
