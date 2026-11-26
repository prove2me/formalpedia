-- Prove2me | Theorems.Thm_O3_Stage2RouteA_hasDerivAt_linePower
-- name    : O3.Stage2RouteA.hasDerivAt_linePower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:31:37.986517+00:00
-- url     : https://prove2.me/theorems/ed97803a-b861-48e7-83b2-f519aa0868d2
-- title:
--   Stage2 Route A: has Deriv At line Power
-- statement:
--   The Stage2 Route A construction uses the has Deriv At line Power property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteA.lean#L34-L46
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteA.lean#L34-L46

import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage2RouteA
set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteA

theorem O3.Stage2RouteA.hasDerivAt_linePower {p : ℝ} (hp : 1 < p) {d : ℕ}
    (x h : Point d) (t : ℝ) :
    HasDerivAt (linePower p x h) (linePowerDerivative p x h t) t := by sorry
