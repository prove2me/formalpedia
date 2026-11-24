-- Prove2me | Theorems.Thm_LefebvreVariations_sidorenko_complete_bipartite
-- name    : LefebvreVariations.sidorenko_complete_bipartite
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-24T23:10:36.850265+00:00
-- url     : https://prove2.me/theorems/a631e61d-2807-46ab-841f-36208f35d357
-- title:
--   Lefebvre's variations: Sidorenko's conjecture for every complete bipartite graph
-- statement:
--   This is Sidorenko's conjecture for every complete bipartite graph.
--
--   Let $G$ be a finite simple graph on $n\ge1$ vertices and let $t(H,G)$ denote the homomorphism density of $H$ in $G$ (the number of edge-preserving maps $V(H)\to V(G)$ divided by $n^{|V(H)|}$). For all $s,t\ge0$,
--
--   $$
--   t(K_{s,t},G)\ \ge\ t(K_2,G)^{\,st}.
--   $$
--
--   With $c(\varphi)$ the number of common neighbours of the images of a map $\varphi$ of the $s$ left vertices, $\hom(K_{s,t},G)=\sum_\varphi c(\varphi)^t$ and $\sum_\varphi c(\varphi)=\sum_w\deg(w)^s$. The power-mean inequality of order $t$ over the $n^s$ tuples, followed by the power-mean inequality of order $s$ over the vertices, gives the claim.
--
--   Sidorenko's conjecture asserts $t(H,G)\ge t(K_2,G)^{e(H)}$ for every bipartite $H$; the complete bipartite graphs were among the first families for which it was proved, and the platform's open cases concern other bipartite graphs with bounded sides. This statement subsumes the stars $K_{1,t}$ and the graphs $K_{2,t}$.
--
--   **Formalization Note** $K_{s,t}$ is `completeBipartiteGraph (Fin s) (Fin t)` and `SidorenkoFor` is the mission's definition; the degenerate cases $s=0$ or $t=0$ are included, where both sides equal $1$.
-- source:
--   A. F. Sidorenko, A correlation inequality for bipartite graphs, Graphs and Combinatorics 9 (1993), 201–204 (Sidorenko's conjecture and its proof for complete bipartite graphs, trees and even cycles); see also L. Lovász, Large Networks and Graph Limits, AMS Colloquium Publications 60, 2012, Section 2.1. Parent problem: TenChallenges.challenge_04 (Sidorenko's conjecture).

import Mathlib
import Definitions.Def_TenChallenges_Sidorenko

open SimpleGraph

namespace LefebvreVariations

/-- Sidorenko's conjecture (Challenge 04), all complete bipartite graphs `K_{s,t}`
(this contains the rung `r = 3` graph `K_{3,3}` and the `K_{2,t}` family).
`hom(K_{s,t}, G) = ∑_{φ : [s] → V} c(φ)^t` with `c(φ)` the number of common neighbours of
the image; Jensen (power mean of order `t`) gives `≥ n^s (n^{-s} ∑ c)^t`, and
`∑_φ c(φ) = ∑_w deg(w)^s ≥ n (2e/n)^s` by Jensen again (power mean of order `s`), which is
exactly `t(K_2,G)^{st}`.
Source: Sidorenko, "A correlation inequality for bipartite graphs", Graphs Combin. 9
(1993), 201-204 (complete bipartite graphs; Theorem 1 as cited for the `K_{2,t}` draft). -/
theorem sidorenko_complete_bipartite (s t : ℕ) {V : Type} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) :
    SidorenkoFor (completeBipartiteGraph (Fin s) (Fin t)) G := by
  sorry

end LefebvreVariations
