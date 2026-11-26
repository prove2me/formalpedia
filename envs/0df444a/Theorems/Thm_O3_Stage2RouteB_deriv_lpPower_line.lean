-- Prove2me | Theorems.Thm_O3_Stage2RouteB_deriv_lpPower_line
-- name    : O3.Stage2RouteB.deriv_lpPower_line
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:21:53.680703+00:00
-- url     : https://prove2.me/theorems/3049b713-3af8-4d45-a45d-e777eb7b443e
-- title:
--   Stage2 Route B: deriv lp Power line
-- statement:
--   The Stage2 Route B construction uses the deriv lp Power line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteB.lean#L91-L109
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage2RouteB.lean#L91-L109

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_Stage2RouteB
set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteB

theorem O3.Stage2RouteB.deriv_lpPower_line {p : ℝ} (hp : 1 < p) {d : ℕ}
    (x h : Point d) (t : ℝ) :
    deriv (fun s : ℝ ↦ lpPower p (fun i ↦ x i + s * h i)) t =
      p * pairing (powerDualityMap p (fun i ↦ x i + t * h i)) h := by sorry
