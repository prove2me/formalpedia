-- Prove2me | Theorems.Thm_InfoNudge_Cutoff_eq_4_th_bounds
-- name    : InfoNudge.Cutoff.eq_4_th_bounds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:10:42.208199+00:00
-- url     : https://prove2.me/theorems/a59f3c40-4d1c-4d94-898c-796fffb6b193
-- title:
--   (3)–(4), pp. 9–10 — the cutoffs satisfy tᵃ ∈ (0, 1) and tʰ ∈ (0, tᵃ)
-- statement:
--   Let $\beta\in(0,1)$, $\delta\in(0,1]$, $C$ with $\beta\delta^2C>1$, and let
--   $$t^a=\frac1{\beta\delta^2C},\qquad t^h=\frac{1+\beta\delta}{1+\delta}\,t^a.$$
--   Then
--   $$0<t^a<1\qquad\text{and}\qquad 0<t^h<t^a.$$
--
--   The cutoff $t^a$ is the belief above which both selves abstain, and $t^h$ is the belief above which the date-0 self would prefer abstaining at both dates to consuming at both dates. The gap $(t^h,t^a)$ is the region of harmful consumption, which exists because $\beta<1$.
-- source:
--   Mariotti, Schweizer, Szech & von Wangenheim, Information Nudges and Self-Control, KIT Working Paper Series in Economics No. 119 (November 2018), pp. 9–10, eqs. (3)–(4)

import Mathlib
import Definitions.Def_InfoNudge_Cutoff_Model

namespace InfoNudge.Cutoff

theorem eq_4_th_bounds (M : Params) (hS : Standing M) :
    0 < ta M ∧ ta M < 1 ∧ 0 < th M ∧ th M < ta M := by sorry

end InfoNudge.Cutoff
