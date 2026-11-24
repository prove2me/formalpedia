-- Prove2me | Theorems.Thm_LefebvreVariations_sidorenko_k2t
-- name    : LefebvreVariations.sidorenko_k2t
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-24T22:36:50.029807+00:00
-- url     : https://prove2.me/theorems/08749788-e61a-46c9-83f5-0edad52fb2bc
-- title:
--   Lefebvre's variations, No. 26 — on a theme by Sidorenko: Sidorenko's conjecture for $K_{2,t}$
-- statement:
--   This is Sidorenko's conjecture for the complete bipartite graphs $K_{2,t}$.
--
--   Let $G$ be a finite simple graph on $n\ge1$ vertices, and let $t(H,G)$ denote the homomorphism density of $H$ in $G$ (the number of edge-preserving maps $V(H)\to V(G)$ divided by $n^{|V(H)|}$). For every $t\ge0$,
--
--   $$
--   t(K_{2,t},G)\ \ge\ t(K_2,G)^{\,2t}.
--   $$
--
--   Writing $c(u,v)$ for the number of common neighbours of $u$ and $v$, one has $t(K_{2,t},G)=n^{-(t+2)}\sum_{u,v}c(u,v)^t$, and the inequality follows from the power-mean inequality over the $n^2$ pairs together with $\sum_{u,v}c(u,v)=\sum_w\deg(w)^2\ge\frac1n\big(\sum_w\deg w\big)^2$.
--
--   Sidorenko's conjecture asserts $t(H,G)\ge t(K_2,G)^{e(H)}$ for every bipartite $H$. The case $t=2$ ($K_{2,2}=C_4$) is classical; the family $K_{2,t}$ for all $t$ falls into the open bounded-side cases of the challenge.
--
--   **Formalization Note** $K_{2,t}$ is `completeBipartiteGraph (Fin 2) (Fin t)` and `SidorenkoFor` is the mission's definition; $t=0$ is included, where both sides equal $1$.
-- source:
--   A. F. Sidorenko, A correlation inequality for bipartite graphs, Graphs and Combinatorics 9 (1993), 201–204 (Sidorenko's conjecture and its proof for complete bipartite graphs, trees and even cycles); for C_4 see also L. Lovász, Large Networks and Graph Limits, AMS Colloquium Publications 60, 2012, Section 2.1. Parent problem: TenChallenges.challenge_04 (Sidorenko's conjecture).

import Mathlib
import Definitions.Def_TenChallenges_Sidorenko

open SimpleGraph

namespace LefebvreVariations

/-- Sidorenko's conjecture (Challenge 04), the complete bipartite graphs `K_{2,t}`
(`K_{2,2} = C_4` is the first even cycle): since `hom(K_{2,t}, G) = ∑_{u,v} c(u,v)^t`
with `c(u,v)` the number of common neighbours, the power-mean inequality gives
`≥ n^2 (n^{-2} ∑ c)^t`, and `∑_{u,v} c(u,v) = ∑_w deg(w)^2 ≥ (2e)^2 / n` by
Cauchy-Schwarz; this is exactly `t(K_2,G)^{2t}`.
Source: Sidorenko, "A correlation inequality for bipartite graphs", Graphs Combin. 9
(1993), 201-204 (complete bipartite graphs; Theorem 1 there); for `C_4` already
Erdős-Simonovits, "Compactness results in extremal graph theory", Combinatorica 2
(1982), 275-288, and Lovász, *Large Networks and Graph Limits*, AMS 2012, Section 2.1. -/
theorem sidorenko_k2t (t : ℕ) {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V) :
    SidorenkoFor (completeBipartiteGraph (Fin 2) (Fin t)) G := by
  sorry

end LefebvreVariations
