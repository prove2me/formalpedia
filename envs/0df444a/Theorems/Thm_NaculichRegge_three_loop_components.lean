-- Prove2me | Theorems.Thm_NaculichRegge_three_loop_components
-- name    : NaculichRegge.three_loop_components
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-26T00:03:03.447807+00:00
-- url     : https://prove2.me/theorems/a756fd14-2b02-4791-b48e-0ec3390cfa6d
-- title:
--   Three-loop Regge basis in the extended trace basis (eq. (4.20))
-- statement:
--   The components of $\{N^3C_{00},N^2C_{11},NC_{21},NC_{22},C_{31},C_{32},C_{33}\}$ in the three-loop extended trace basis $t^{(3)}_1,\dots,t^{(3)}_{12}$ are those of eq. (4.20):
--   $$\begin{aligned}N^3C_{00}&=(1,0,-1,0,0,0,0,0,0,0,0,0),\\N^2C_{11}&=(-\tfrac12,0,-\tfrac12,-2,-2,-2,0,0,0,0,0,0),\\NC_{21}&=(0,0,0,-2,4,-2,2,-4,2,0,0,0),\\NC_{22}&=(\tfrac14,0,-\tfrac14,-3,0,3,3,0,-3,0,0,0),\\C_{31}&=(0,0,0,-2,-4,-2,2,-8,2,-8,-8,-8),\\C_{32}&=(0,0,0,-1,0,1,-5,0,5,0,0,0),\\C_{33}&=(-\tfrac18,0,-\tfrac18,-\tfrac72,-\tfrac12,-\tfrac72,-3,3,-3,-6,-6,-6).\end{aligned}$$
-- source:
--   S. G. Naculich, "All-loop-orders relation between Regge limits of N = 4 SYM and N = 8 supergravity four-point amplitudes", arXiv:2012.00030v2, https://arxiv.org/abs/2012.00030, p. 15, eq. (4.20)

import Definitions.Def_NaculichRegge_TraceBasis

open Polynomial

namespace NaculichRegge

/-- Naculich, eq. (4.20): the components of the three-loop Regge basis in the extended trace
basis `t_1^{(3)}, …, t_{12}^{(3)}`. -/
theorem three_loop_components :
    (List.range 12).map (fun m => extCoord 3 ((X : ℂ[X]) ^ 3 • reggeColor 0 0) (m + 1)) =
        [1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0] ∧
    (List.range 12).map (fun m => extCoord 3 ((X : ℂ[X]) ^ 2 • reggeColor 1 1) (m + 1)) =
        [-1/2, 0, -1/2, -2, -2, -2, 0, 0, 0, 0, 0, 0] ∧
    (List.range 12).map (fun m => extCoord 3 ((X : ℂ[X]) • reggeColor 2 1) (m + 1)) =
        [0, 0, 0, -2, 4, -2, 2, -4, 2, 0, 0, 0] ∧
    (List.range 12).map (fun m => extCoord 3 ((X : ℂ[X]) • reggeColor 2 2) (m + 1)) =
        [1/4, 0, -1/4, -3, 0, 3, 3, 0, -3, 0, 0, 0] ∧
    (List.range 12).map (fun m => extCoord 3 (reggeColor 3 1) (m + 1)) =
        [0, 0, 0, -2, -4, -2, 2, -8, 2, -8, -8, -8] ∧
    (List.range 12).map (fun m => extCoord 3 (reggeColor 3 2) (m + 1)) =
        [0, 0, 0, -1, 0, 1, -5, 0, 5, 0, 0, 0] ∧
    (List.range 12).map (fun m => extCoord 3 (reggeColor 3 3) (m + 1)) =
        [-1/8, 0, -1/8, -7/2, -1/2, -7/2, -3, 3, -3, -6, -6, -6] := by sorry

end NaculichRegge
