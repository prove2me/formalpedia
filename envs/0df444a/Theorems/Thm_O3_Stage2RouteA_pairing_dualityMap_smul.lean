-- Prove2me | Theorems.Thm_O3_Stage2RouteA_pairing_dualityMap_smul
-- name    : O3.Stage2RouteA.pairing_dualityMap_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:32:07.964803+00:00
-- url     : https://prove2.me/theorems/929b56d7-d497-5b61-9f62-ca3c62ed3c4b
-- title:
--   Stage2 Route A: pairing duality Map smul
-- statement:
--   Exact radial formula for the normalized duality pairing.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteA.lean#L273-L289
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteA.lean#L273-L289

import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage2RouteA
set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteA

theorem O3.Stage2RouteA.pairing_dualityMap_smul {q : ℝ} (hq : 1 < q) {d : ℕ}
    (a : ℝ) (h : Point d) :
    pairing (dualityMap q (a • h)) h =
      a * (lpNorm q h) ^ (2 : ℕ) := by sorry
