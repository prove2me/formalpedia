-- Prove2me | Theorems.Thm_O3_Stage2RouteA_lineGradientFormula_eq_duality_pair
-- name    : O3.Stage2RouteA.lineGradientFormula_eq_duality_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:32:30.001136+00:00
-- url     : https://prove2.me/theorems/a456b883-1556-4d77-971c-c4a9d25605b6
-- title:
--   Stage2 Route A: line Gradient Formula eq duality pair
-- statement:
--   The Stage2 Route A construction uses the line Gradient Formula eq duality pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteA.lean#L320-L331
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteA.lean#L320-L331

import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage2RouteA
set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteA

theorem O3.Stage2RouteA.lineGradientFormula_eq_duality_pair {p : ℝ} (hp : p ≠ 0) {d : ℕ}
    (x h : Point d) (t : ℝ) (hz : x + t • h ≠ 0) :
    lineGradientFormula p x h t = pairing (dualityMap p (x + t • h)) h := by sorry
