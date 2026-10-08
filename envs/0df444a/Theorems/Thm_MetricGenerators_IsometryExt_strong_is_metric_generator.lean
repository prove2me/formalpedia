-- Prove2me | Theorems.Thm_MetricGenerators_IsometryExt_strong_is_metric_generator
-- name    : MetricGenerators.IsometryExt.strong_is_metric_generator
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:12:58.603974+00:00
-- url     : https://prove2.me/theorems/682bcc6f-ce15-45d6-a904-7832d537d0aa
-- title:
--   §2, p. 386 — a strong metric generator is a metric generator
-- statement:
--   Let $G$ be a finite connected graph and $S\subseteq V(G)$ a strong metric generator of $G$: for every pair $x,y$ of vertices there is $s\in S$ with $\mu_G(s,x)=\mu_G(s,y)+\mu_G(y,x)$ or $\mu_G(s,y)=\mu_G(s,x)+\mu_G(x,y)$. Then $S$ is a metric generator of $G$:
--   $$\forall x\ne y\in V(G)\ \ \exists s\in S:\ \ \mu_G(s,x)\ne\mu_G(s,y).$$
--
--   The paper notes this right after defining strong metric generators; Figure 1 of the paper shows that the converse fails. It lets the later arguments use the disjointness that a metric generator provides.
--
--   **Formalization Note** Connectivity is the paper's standing assumption; distances are $\mathbb N$-valued.
-- source:
--   Sebő and Tannier, On Metric Generators of Graphs, Math. Oper. Res. 29(2):383–393 (2004), DOI 10.1287/moor.1030.0070, p. 386, §2 (unnumbered, paragraph after the definition of a strong metric generator)

import Mathlib
import Definitions.Def_MetricGenerators_IsometryExt_Basic

namespace MetricGenerators.IsometryExt

/-- Sebő and Tannier, *On Metric Generators of Graphs*, Math. Oper. Res. 29(2):383–393 (2004),
DOI 10.1287/moor.1030.0070, §2, p. 386 (unnumbered): "a strong metric generator is always a metric generator".

Formalization Note: stated for a finite connected graph (the paper's standing assumption, p. 383;
the definition of a strong metric generator is made for connected graphs). -/
theorem strong_is_metric_generator {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hG : G.Connected) (S : Finset V) (hS : IsStrongMetricGenerator G S) :
    IsMetricGenerator G S := by sorry

end MetricGenerators.IsometryExt
