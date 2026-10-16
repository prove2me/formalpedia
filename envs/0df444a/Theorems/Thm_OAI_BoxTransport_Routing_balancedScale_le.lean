-- Prove2me | Theorems.Thm_OAI_BoxTransport_Routing_balancedScale_le
-- name    : OAI.BoxTransport.Routing.balancedScale_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T13:17:17.437768+00:00
-- url     : https://prove2.me/theorems/6bb35e1f-c0be-406d-8c32-b40d43aed612
-- title:
--   Coordinates of a volume-preserving scale blend are bounded by $\max(1,s_j)$
-- statement:
--   Let $s=(s_1,s_2,s_3)\in\mathbb{R}^3$ with $s_j>0$ for all $j$ and $s_1s_2s_3=1$. For $u\in\mathbb{R}$ define the balanced scale
--
--   $$\beta(s,u)=\Big(1-u+us_1,\ \ 1-u+us_2,\ \ \big((1-u+us_1)(1-u+us_2)\big)^{-1}\Big).$$
--
--   **Theorem.** For every $u\in[0,1]$ and every $j\in\{1,2,3\}$,
--
--   $$\beta(s,u)_j\le\max(1,s_j).$$
--
--   For $u\in[0,1]$ the vectors $\beta(s,u)$ have positive coordinates with product $1$, and they interpolate between $\beta(s,0)=(1,1,1)$ and $\beta(s,1)=s$ (because $s_3=(s_1s_2)^{-1}$). The theorem says that along this volume-preserving deformation no stretching factor ever exceeds $\max(1,s_j)$. This provides the uniform upper bound on the scale factors that is needed when the deformation of a box is realized by a smooth incompressible flow.
--
--   **Formalization Note** The vector $\beta(s,u)$ is `balancedScale s u`, and its third coordinate uses Lean's inverse (with $0^{-1}=0$); under the hypotheses the two blends are positive, so the inverse is the genuine one.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BoxTransport/Motion.lean#L307-L324

import Mathlib
import Definitions.Def_BalancedBoxRouting
import Definitions.Def_OAI_Analysis_BoxTransport_Geometry
import Definitions.Def_OAI_Analysis_BoxTransport_Flow
import Definitions.Def_OAI_Analysis_BoxTransport_Motion

open OAI OAI.BoxTransport OAI.BoxTransport.Routing
open scoped Topology
open scoped BigOperators ContDiff

theorem OAI.BoxTransport.Routing.balancedScale_le (s : Space) (hs : ∀ j, 0 < s j)
    (hdet : ∏ j : Fin 3, s j = 1) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) (j : Fin 3) :
    balancedScale s u j ≤ max 1 (s j) := by sorry
