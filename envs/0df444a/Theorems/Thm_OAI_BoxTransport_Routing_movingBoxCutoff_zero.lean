-- Prove2me | Theorems.Thm_OAI_BoxTransport_Routing_movingBoxCutoff_zero
-- name    : OAI.BoxTransport.Routing.movingBoxCutoff_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T13:13:24.026317+00:00
-- url     : https://prove2.me/theorems/52123991-9758-41c6-bbe8-7e7360abafbc
-- title:
--   The moving box cutoff vanishes outside the open box padded by $2\eta$
-- statement:
--   Let $c,r:\mathbb{R}\to\mathbb{R}^3$ be arbitrary curves (a moving center and moving half-widths) and let $\eta>0$. Let $S$ be the standard smooth transition function, $S(y)=\psi(y)/(\psi(y)+\psi(1-y))$ with $\psi(y)=e^{-1/y}$ for $y>0$ and $\psi(y)=0$ for $y\le0$; in particular $S(y)=0$ for $y\le0$. The moving box cutoff is the function on $\mathbb{R}\times\mathbb{R}^3$
--
--   $$\chi(t,x)=\prod_{j=1}^{3}S\Big(\frac{r_j(t)+2\eta+(x_j-c_j(t))}{\eta}\Big)\,S\Big(\frac{r_j(t)+2\eta-(x_j-c_j(t))}{\eta}\Big).$$
--
--   **Theorem.** Let $(t,x)\in\mathbb{R}\times\mathbb{R}^3$. If $x$ does not belong to the open box
--
--   $$\{y\in\mathbb{R}^3:\ |y_j-c_j(t)|<r_j(t)+2\eta\ \text{ for } j=1,2,3\},$$
--
--   then $\chi(t,x)=0$.
--
--   The cutoff is therefore supported in the closure of the moving box padded by $2\eta$. Together with the complementary fact that $\chi=1$ on the box padded by $\eta$, it localizes the potential attached to each box to a thin neighbourhood of that box; this keeps the contributions of different (separated) boxes from interacting and yields compact support of the routed field.
--
--   **Formalization Note** The cutoff is `movingBoxCutoff c r η`, built from Mathlib's `Real.smoothTransition`, and the open box is `openBox (c t) (r t) (2 * η)`. Space-time points are pairs `p : SpaceTime` with time `p.1` and position `p.2`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BoxTransport/Flow.lean#L255-L274

import Mathlib
import Definitions.Def_BalancedBoxRouting
import Definitions.Def_OAI_Analysis_BoxTransport_Geometry
import Definitions.Def_OAI_Analysis_BoxTransport_Flow

open OAI OAI.BoxTransport OAI.BoxTransport.Routing
open scoped Topology
open scoped BigOperators ContDiff

theorem OAI.BoxTransport.Routing.movingBoxCutoff_zero {c r : ℝ → Space} {η : ℝ} (hη : 0 < η)
    {p : SpaceTime} (hp : p.2 ∉ openBox (c p.1) (r p.1) (2 * η)) :
    movingBoxCutoff c r η p = 0 := by sorry
