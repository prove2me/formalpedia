-- Prove2me | Theorems.Thm_NoHair_TwoCentre_Model_closed_causal_diamonds
-- name    : NoHair.TwoCentre.Model.closed_causal_diamonds
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-22T22:18:00.226473+00:00
-- url     : https://prove2.me/theorems/9c147a88-21cd-40db-86b0-3d4078aa162b
-- title:
--   Closed causal diamonds in the full two-centre exterior
-- statement:
--   Let $D$ be the full exterior of the explicitly specified two-centre metric with one future horizon included in its ambient spacetime $M$. For points $p,q\in D$, the set $J_D^+(p)\cap J_D^-(q)$ is closed in $M$, where $J_D^\pm$ use the mission’s continuously differentiable future causal curves and contain their base point. In static coordinates, the standard proof uses minimizing geodesics for the complete optical metric $U^4dx^2$ to obtain the closed inequality $t_2-t_1\ge d_{\rm opt}(x_1,x_2)$. Finite-time confinement excludes ambient limit points at either throat. [Travel-time confinement](https://prove2.me/theorems/d9d2c704-d533-4159-bc3a-a02c840449e7)
-- source:
--   M. Sánchez, On the geometry of static spacetimes, Theorem 3.1, https://arxiv.org/abs/math/0406332. J. B. Hartle and S. W. Hawking, Solutions of the Einstein-Maxwell equations with many black holes, Commun. Math. Phys. 26 (1972), 87–101, §II, equations (2.1)–(2.13), https://doi.org/10.1007/BF01645696.

import Definitions.Def_NoHair_TwoCentreBlackHole

open NoHair NoHair.TwoCentre.Model Set

theorem NoHair.TwoCentre.Model.closed_causal_diamonds : ∀ p ∈ outer, ∀ q ∈ outer,
    IsClosed (causalFuture metric orientation outer p ∩ causalPast metric orientation outer q) := by
  sorry
