-- Prove2me | Theorems.Thm_OAI_BoxTransport_Routing_deriv_zero_outside_interval
-- name    : OAI.BoxTransport.Routing.deriv_zero_outside_interval
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T13:15:10.014698+00:00
-- url     : https://prove2.me/theorems/d940ed02-fc46-472e-a57a-448c8e9968e1
-- title:
--   A path constant before $u$ and after $v$ has zero derivative outside $[u,v]$
-- statement:
--   Let $f:\mathbb{R}\to\mathbb{R}^3$, $a,b\in\mathbb{R}^3$ and $u,v,t\in\mathbb{R}$. Suppose that $f(s)=a$ for all $s\le u$ and $f(s)=b$ for all $s\ge v$.
--
--   **Theorem.** If $t\notin[u,v]$, then
--
--   $$f'(t)=0 .$$
--
--   A path that is stationary before time $u$ and after time $v$ has zero velocity outside $[u,v]$. In the box-routing construction this shows that the velocities of the box centers and the rates of change of the box scalings vanish for times outside $[1/4,3/4]$, so that the routed velocity field is switched off there.
--
--   **Formalization Note** The derivative is Mathlib's `deriv f t`, which is defined to be $0$ at points of non-differentiability. Under the hypotheses $f$ is constant on a neighbourhood of $t$, so $f$ is in fact differentiable at $t$ and its derivative there is $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BoxTransport/Flow.lean#L663-L677

import Mathlib
import Definitions.Def_BalancedBoxRouting
import Definitions.Def_OAI_Analysis_BoxTransport_Geometry
import Definitions.Def_OAI_Analysis_BoxTransport_Flow

open OAI OAI.BoxTransport OAI.BoxTransport.Routing
open scoped Topology
open scoped BigOperators ContDiff

theorem OAI.BoxTransport.Routing.deriv_zero_outside_interval {f : ℝ → Space} {a b : Space} {u v t : ℝ}
    (hbefore : ∀ s, s ≤ u → f s = a) (hafter : ∀ s, v ≤ s → f s = b)
    (ht : t ∉ Set.Icc u v) : deriv f t = 0 := by sorry
