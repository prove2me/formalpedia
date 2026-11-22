-- Prove2me | Theorems.Thm_NoHair_kerr_inner_horizon_shell_not_exterior
-- name    : NoHair.kerr_inner_horizon_shell_not_exterior
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-22T22:54:21.060259+00:00
-- url     : https://prove2.me/theorems/3a0b5180-4b38-4b4d-84d1-77ebcb383e48
-- title:
--   The region outside the inner Kerr horizon contains trapped observers
-- statement:
--   For the Kerr spacetime with $m=5/2$ and $a=2$, the region $A=\{r>1\}$ is not isometric to the standard domain of outer communications of any admissible vacuum Kerr solution. Every point in a standard Kerr exterior lies on a complete unit-speed timelike curve at fixed radius and latitude. At $r=2$ in $A$ the gradient of the Kerr radius is timelike. Along the decreasing direction of any unit-speed timelike curve starting there, the radius approaches the excluded inner boundary in bounded proper time.
-- source:
--   M. Visser, The Kerr spacetime: A brief introduction, §§5 and 9, equations (32)–(38) and (88)–(94), https://arxiv.org/abs/0706.0622. The invariant uses the inverse radial metric coefficient and the timelike linear combination of the stationary and axial Killing fields.

import Definitions.Def_NoHair_kerrNewman

open NoHair Set
open scoped ContDiff Manifold

theorem NoHair.kerr_inner_horizon_shell_not_exterior (μ b : ℝ) (hp : IsKerrNewmanBlackHoleParams μ b 0) :
    ¬ IsKerrNewmanDOC (kerrNewmanMetricField (5/2) 2 0) (kerrNewmanFieldField 2 0) {x : kerrNewmanSpacetime 2 | 1 < ksRadius 2 x.val} μ b 0 := by
  sorry
