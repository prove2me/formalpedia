-- Prove2me | Theorems.Thm_O3_Stage2RouteA_hasDerivAt_lineEnergy_of_ne_zero
-- name    : O3.Stage2RouteA.hasDerivAt_lineEnergy_of_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:33:12.192693+00:00
-- url     : https://prove2.me/theorems/a0382905-aec7-4dfb-92d8-aa1cd52f6856
-- title:
--   Stage2 Route A: has Deriv At line Energy of ne zero
-- statement:
--   The Stage2 Route A construction uses the has Deriv At line Energy of ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteA.lean#L76-L110
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteA.lean#L76-L110

import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage2RouteA
set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteA

theorem O3.Stage2RouteA.hasDerivAt_lineEnergy_of_ne_zero {p : ℝ} (hp : 1 < p) {d : ℕ}
    (x h : Point d) (t : ℝ) (hz : x + t • h ≠ 0) :
    HasDerivAt (lineEnergy p x h)
      (pairing (dualityMap p (x + t • h)) h) t := by sorry
