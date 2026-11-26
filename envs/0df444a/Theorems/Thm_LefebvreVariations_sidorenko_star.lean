-- Prove2me | Theorems.Thm_LefebvreVariations_sidorenko_star
-- name    : LefebvreVariations.sidorenko_star
-- status  : Proved
-- author  : @Secousses
-- created : 2026-11-24T21:59:25.777795+00:00
-- url     : https://prove2.me/theorems/c622146d-52cf-41f5-b9b5-296f82669538
-- title:
--   Lefebvre's variations, No. 3 — on a theme by Sidorenko: Sidorenko's conjecture for stars $K_{1,t}$
-- statement:
--   This is the case of stars of Sidorenko's conjecture (Ten Challenges 04).
--
--   Let $G$ be a finite simple graph on $n\ge1$ vertices and, for a graph $H$, let $t(H,G)$ be the homomorphism density of $H$ in $G$: the number of maps $V(H)\to V(G)$ sending edges to edges, divided by $n^{|V(H)|}$. For every $t\ge0$, the star $K_{1,t}$ (one centre joined to $t$ leaves) satisfies
--
--   $$
--   t(K_{1,t},G)\ \ge\ t(K_2,G)^{\,t}.
--   $$
--
--   Since $t(K_{1,t},G)=n^{-(t+1)}\sum_v \deg(v)^t$ and $t(K_2,G)=n^{-2}\sum_v\deg(v)$, the inequality is the power-mean inequality for the degree sequence. Sidorenko's conjecture asserts $t(H,G)\ge t(K_2,G)^{e(H)}$ for every bipartite $H$; stars (and, more generally, trees) are among the first families for which it was established, and this case covers the side-length-one instances of the open bounded-side cases of the challenge.
--
--   **Formalization Note** The star is `completeBipartiteGraph Unit (Fin t)`; homomorphism densities and `SidorenkoFor` are the mission's definitions. The case $t=0$ is included, where both sides equal $1$.
--
--   **Why this is a variation.** This varies Sidorenko's conjecture (`TenChallenges.challenge_04`): $t(H,G)\ge t(K_2,G)^{e(H)}$ for every bipartite graph $H$. It is the special case of the stars $K_{1,t}$, the simplest bipartite graphs, where the inequality is the power-mean inequality on the degree sequence. Settling it covers the instances of the parent in which one side has a single vertex.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   A. F. Sidorenko, A correlation inequality for bipartite graphs, Graphs and Combinatorics 9 (1993), 201–204 (the conjecture holds for trees, in particular stars). For stars the statement is the power-mean inequality for degrees; for paths see G. R. Blakley and P. Roy, A Hölder type inequality for symmetric matrices with nonnegative entries, Proc. Amer. Math. Soc. 16 (1965), 1244–1245. Parent problem: TenChallenges.challenge_04 (Sidorenko's conjecture).

import Mathlib
import Definitions.Def_TenChallenges_Sidorenko

open SimpleGraph

namespace LefebvreVariations

/-- Sidorenko's conjecture (Challenge 04), the case of stars `K_{1,t}`: since
`t(K_{1,t}, G) = n^{-(t+1)} ∑_v deg(v)^t` and `t(K_2, G) = n^{-2} ∑_v deg(v)`, the
inequality is the power-mean (Jensen) inequality for `x ↦ x^t`.
Source: Sidorenko, "A correlation inequality for bipartite graphs", Graphs
Combin. 9 (1993), 201-204 (stars and trees); Blakley–Roy 1965 for paths. -/
theorem sidorenko_star (t : ℕ) {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V) :
    SidorenkoFor (completeBipartiteGraph Unit (Fin t)) G := by
  sorry

end LefebvreVariations
