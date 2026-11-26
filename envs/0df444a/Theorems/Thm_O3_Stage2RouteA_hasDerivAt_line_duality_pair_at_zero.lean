-- Prove2me | Theorems.Thm_O3_Stage2RouteA_hasDerivAt_line_duality_pair_at_zero
-- name    : O3.Stage2RouteA.hasDerivAt_line_duality_pair_at_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:32:16.47374+00:00
-- url     : https://prove2.me/theorems/2759cb2a-88f1-587c-bafb-951786258776
-- title:
--   Stage2 Route A: has Deriv At line duality pair at zero
-- statement:
--   The Stage2 Route A construction uses the has Deriv At line duality pair at zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteA.lean#L305-L312
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteA.lean#L305-L312

import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage2RouteA
set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteA

theorem O3.Stage2RouteA.hasDerivAt_line_duality_pair_at_zero {q : ℝ} (hq : 1 < q) {d : ℕ}
    (x h : Point d) (t : ℝ) (hz : x + t • h = 0) :
    HasDerivAt (fun s : ℝ ↦ pairing (dualityMap q (x + s • h)) h)
      ((lpNorm q h) ^ (2 : ℕ)) t := by sorry
