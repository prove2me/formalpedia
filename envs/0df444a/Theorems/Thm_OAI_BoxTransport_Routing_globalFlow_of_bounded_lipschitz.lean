-- Prove2me | Theorems.Thm_OAI_BoxTransport_Routing_globalFlow_of_bounded_lipschitz
-- name    : OAI.BoxTransport.Routing.globalFlow_of_bounded_lipschitz
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T13:13:55.10398+00:00
-- url     : https://prove2.me/theorems/9393b496-b3e9-4784-b9e7-b77d1b68602b
-- title:
--   Bounded vector fields that are uniformly Lipschitz in space have unique global flows
-- statement:
--   Let $U:\mathbb{R}\times\mathbb{R}^3\to\mathbb{R}^3$ be a time-dependent vector field and let $M,K\ge0$. Assume that $U$ is continuous, that $\|U(t,x)\|\le M$ for all $(t,x)$, and that for every $t$ the map $x\mapsto U(t,x)$ is $K$-Lipschitz, i.e. $\|U(t,x)-U(t,y)\|\le K\|x-y\|$ for all $x,y\in\mathbb{R}^3$, with $K$ independent of $t$.
--
--   **Theorem.** There is a map $\Phi:\mathbb{R}\times\mathbb{R}^3\to\mathbb{R}^3$ (a global flow of $U$) such that for every $x\in\mathbb{R}^3$
--
--   $$\Phi(0,x)=x,\qquad \frac{\partial}{\partial t}\Phi(t,x)=U\big(t,\Phi(t,x)\big)\quad\text{for all } t\in\mathbb{R},$$
--
--   and every curve $\gamma:\mathbb{R}\to\mathbb{R}^3$ with $\gamma(0)=x$ and $\gamma'(t)=U(t,\gamma(t))$ for all $t\in\mathbb{R}$ satisfies $\gamma(t)=\Phi(t,x)$ for all $t\in\mathbb{R}$.
--
--   This is a global form of the Picard–Lindelöf (Cauchy–Lipschitz) theorem: the uniform bound and the uniform spatial Lipschitz constant exclude blow-up, so every trajectory exists for all times, and trajectories are unique. In the box-routing construction it is applied to smooth compactly supported velocity fields, which satisfy both hypotheses automatically.
--
--   **Formalization Note** Points of $\mathbb{R}^3$ are functions on `Fin 3` with the maximum norm $\|x\|=\max_j|x_j|$; $M$ and $K$ are of type `NNReal`, and the Lipschitz condition is `LipschitzWith K (fun x => U (t, x))`. The three flow properties form the predicate `IsGlobalFlow U Φ`, with derivatives expressed by `HasDerivAt`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BoxTransport/Flow.lean#L463-L536

import Mathlib
import Definitions.Def_BalancedBoxRouting
import Definitions.Def_OAI_Analysis_BoxTransport_Geometry
import Definitions.Def_OAI_Analysis_BoxTransport_Flow

open OAI OAI.BoxTransport OAI.BoxTransport.Routing
open scoped Topology
open scoped BigOperators ContDiff

theorem OAI.BoxTransport.Routing.globalFlow_of_bounded_lipschitz {U : Field} {M K : NNReal}
    (hcont : Continuous U) (hbound : ∀ p, ‖U p‖ ≤ M)
    (hlip : ∀ t, LipschitzWith K (fun x => U (t, x))) :
    ∃ Φ, IsGlobalFlow U Φ := by sorry
