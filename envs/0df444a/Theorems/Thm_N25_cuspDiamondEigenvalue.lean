-- Prove2me | Theorems.Thm_N25_cuspDiamondEigenvalue
-- name    : N25.cuspDiamondEigenvalue
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:03:24.664077+00:00
-- url     : https://prove2.me/theorems/97eeeaa0-eb43-441c-9221-79207e87b675
-- title:
--   The basic cusp class has diamond eigenvalues $5$ and $57$
-- statement:
--   Let $p_0,p_1,p_2$ be the first three selected geometric cusps and put $t=[p_0-p_1]$ in the Jacobian $J$. Assume $[p_0-p_2]=6t$ and $71t=0$. If $\gamma$ is the distinguished label-$13$ diamond action and $\delta_2$ is the label-$2$ diamond action, then
--
--   $$\gamma(t)=5t\quad\text{and}\quad\delta_2(t)=57t.$$
--
--   This identifies the two diamond eigenvalues carried by the rational cuspidal line.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_SelectedCusps
import Definitions.Def_N25_PointDifference
import Theorems.Thm_N25_Endgame_pG25_degree
import Theorems.Thm_ModularCurve_diamondHBar_mul
import Theorems.Thm_ModularCurve_diamondHBar_apply_eq_self_of_mem

set_option autoImplicit false
open N25
open AlgebraicCurve N25.Endgame

theorem N25.cuspDiamondEigenvalue
    (hcoeff : pointDiff (pG25 0) (pG25 2)
        ((pG25_degree 0).trans (pG25_degree 2).symm) =
      (6 : ℤ) • pointDiff (pG25 0) (pG25 1)
        ((pG25_degree 0).trans (pG25_degree 1).symm))
    (h71 : (71 : ℤ) • pointDiff (pG25 0) (pG25 1)
        ((pG25_degree 0).trans (pG25_degree 1).symm) = 0) :
    let t : J := pointDiff (pG25 0) (pG25 1)
      ((pG25_degree 0).trans (pG25_degree 1).symm)
    gamma t = (5 : ℤ) • t ∧
      ModularCurve.diamondHBar 25 H25 (ZMod.unitOfCoprime 2 (by decide)) t =
        (57 : ℤ) • t := by sorry
