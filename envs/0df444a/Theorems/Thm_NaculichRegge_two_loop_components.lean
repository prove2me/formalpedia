-- Prove2me | Theorems.Thm_NaculichRegge_two_loop_components
-- name    : NaculichRegge.two_loop_components
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-26T00:02:22.147866+00:00
-- url     : https://prove2.me/theorems/a29bba6f-1e4e-42e2-8f81-1076c4e5bdc5
-- title:
--   Two-loop Regge basis in the extended trace basis (eq. (4.16))
-- statement:
--   The components of $\{N^2C_{00},NC_{11},C_{21},C_{22}\}$ in the two-loop extended trace basis $t^{(2)}_1,\dots,t^{(2)}_9$ are
--   $$\begin{aligned}N^2C_{00}&=(1,0,-1,0,0,0,0,0,0),\\ NC_{11}&=(-\tfrac12,0,-\tfrac12,-2,-2,-2,0,0,0),\\ C_{21}&=(0,0,0,-2,4,-2,2,-4,2),\\ C_{22}&=(\tfrac14,0,-\tfrac14,-3,0,3,3,0,-3).\end{aligned}$$
-- source:
--   S. G. Naculich, "All-loop-orders relation between Regge limits of N = 4 SYM and N = 8 supergravity four-point amplitudes", arXiv:2012.00030v2, https://arxiv.org/abs/2012.00030, p. 14, eq. (4.16)

import Definitions.Def_NaculichRegge_TraceBasis

open Polynomial

namespace NaculichRegge

/-- Naculich, eq. (4.16): the components of the two-loop Regge basis in the extended trace
basis `t_1^{(2)}, …, t_9^{(2)}`. -/
theorem two_loop_components :
    (List.range 9).map (fun m => extCoord 2 ((X : ℂ[X]) ^ 2 • reggeColor 0 0) (m + 1)) =
        [1, 0, -1, 0, 0, 0, 0, 0, 0] ∧
    (List.range 9).map (fun m => extCoord 2 ((X : ℂ[X]) • reggeColor 1 1) (m + 1)) =
        [-1/2, 0, -1/2, -2, -2, -2, 0, 0, 0] ∧
    (List.range 9).map (fun m => extCoord 2 (reggeColor 2 1) (m + 1)) =
        [0, 0, 0, -2, 4, -2, 2, -4, 2] ∧
    (List.range 9).map (fun m => extCoord 2 (reggeColor 2 2) (m + 1)) =
        [1/4, 0, -1/4, -3, 0, 3, 3, 0, -3] := by sorry

end NaculichRegge
