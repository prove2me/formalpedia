-- Prove2me | Theorems.Thm_O3_Stage2RouteA_exists_hasDerivAt_line_duality_pair_le_above_two
-- name    : O3.Stage2RouteA.exists_hasDerivAt_line_duality_pair_le_above_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:33:09.00988+00:00
-- url     : https://prove2.me/theorems/0f6db42d-1c8a-5c6a-911e-9174a6ed34f9
-- title:
--   Stage2 Route A: exists has Deriv At line duality pair le above two
-- statement:
--   Every line parameter admits an exact derivative of the actual normalized
--   duality pairing, together with the sharp `(q-1)` upper bound.  The proof splits
--   only on the whole-vector zero; scalar coordinate zeros are already native.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteA.lean#L438-L464
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteA.lean#L438-L464

import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage2RouteA
set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteA

theorem O3.Stage2RouteA.exists_hasDerivAt_line_duality_pair_le_above_two
    {q : ℝ} (hq : 2 < q) {d : ℕ} (x h : Point d) (t : ℝ) :
    ∃ v : ℝ,
      HasDerivAt (fun s : ℝ ↦ pairing (dualityMap q (x + s • h)) h) v t ∧
        v ≤ (q - 1) * (lpNorm q h) ^ (2 : ℕ) := by sorry
