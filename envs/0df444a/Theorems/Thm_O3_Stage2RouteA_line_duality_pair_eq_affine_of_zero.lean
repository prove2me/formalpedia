-- Prove2me | Theorems.Thm_O3_Stage2RouteA_line_duality_pair_eq_affine_of_zero
-- name    : O3.Stage2RouteA.line_duality_pair_eq_affine_of_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:32:13.020894+00:00
-- url     : https://prove2.me/theorems/861d1c63-2ea4-5c2f-80bc-54256e837c31
-- title:
--   Stage2 Route A: line duality pair eq affine of zero
-- statement:
--   At the unique whole-vector zero on an affine line, the actual normalized
--   duality pairing is locally (indeed globally) affine in the line parameter.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteA.lean#L293-L303
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteA.lean#L293-L303

import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage2RouteA
set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteA

theorem O3.Stage2RouteA.line_duality_pair_eq_affine_of_zero {q : ℝ} (hq : 1 < q) {d : ℕ}
    (x h : Point d) (t : ℝ) (hz : x + t • h = 0) :
    (fun s : ℝ ↦ pairing (dualityMap q (x + s • h)) h) =
      fun s : ℝ ↦ (s - t) * (lpNorm q h) ^ (2 : ℕ) := by sorry
