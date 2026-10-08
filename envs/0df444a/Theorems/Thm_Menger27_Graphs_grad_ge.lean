-- Prove2me | Theorems.Thm_Menger27_Graphs_grad_ge
-- name    : Menger27.Graphs.grad_ge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:15:38.432038+00:00
-- url     : https://prove2.me/theorems/6df701ca-76d3-48e8-928f-c6147e855235
-- title:
--   p. 101, proof of Satz δ — a graph n-point connected between P and Q has at least n edges
-- statement:
--   Let $G$ be a finite simple graph on $V$, let $P, Q \subseteq V$ be disjoint, and let $n \ge 0$. If $G$ is $n$-point connected between $P$ and $Q$ (every vertex set separating $P$ and $Q$ has at least $n$ elements), then the degree of $G$, its number of edges, is at least $n$:
--   $$n \le |E(G)| .$$
--
--   Menger writes: "Man zeigt leicht, dass der Grad jedes zwischen zwei Mengen P und Q n-punktig zusammenhängenden Raumes ≧ n ist". This is the base of his induction on the degree.
--
--   **Formalization Note.** Menger's *Grad* is the number of *zusammenhängende Stücke* of $K(P, Q)$, the open arcs between consecutive end, branch and $P \cup Q$ points. In the graph reading of this mission it is the number of edges, `G.edgeFinset.card`. A subdivided graph has more edges than Menger's Grad; the bound remains true and only becomes weaker.
-- source:
--   Menger, Zur allgemeinen Kurventheorie, Fund. Math. 10 (1927), p. 101, proof of Satz δ

import Mathlib
import Definitions.Def_Menger27_Graphs_Separation

namespace Menger27.Graphs

theorem grad_ge {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (P Q : Finset V) (hPQ : Disjoint P Q) (n : ℕ)
    (hG : NPointConnected G P Q n) :
    n ≤ G.edgeFinset.card := by sorry

end Menger27.Graphs
