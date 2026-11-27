-- Prove2me | Theorems.Thm_GraphMatching_fracVC_eq
-- name    : GraphMatching.fracVC_eq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T04:25:33.440892+00:00
-- url     : https://prove2.me/theorems/f615a3da-5662-5e48-9777-666008aca0be
-- title:
--   $2\,\tau^*(G)=\nu(\text{double cover of }G)$
-- statement:
--   Let $G$ be a finite simple graph on $V$, let $\tau^*(G)$ be its fractional vertex cover number (the minimum of $\sum_v y(v)$ over $y:V\to[0,1]$ with $y(u)+y(v)\ge1$ on every edge), and let $\widetilde G$ be its bipartite double cover on $\{0,1\}\times V$, where $(a,u)\sim(b,v)$ iff $a\ne b$ and $u\sim v$ in $G$. Then
--   $$2\,\tau^*(G)=\nu(\widetilde G).$$
--
--   In the sublinear TSP algorithm the cost $\tau=\sigma\,\tau^*(\Gamma)$ of combining fragment shortenings in a conflict graph $\Gamma$ is estimated by estimating the matching number of the double cover of $\Gamma$; this identity is the bridge $\tau=\tfrac{\sigma}{2}\,\mu$ used there.
--
--   **Formalization Note** The proof combines König's theorem on the double cover with weak LP duality; the minimum fractional cover is attained.
-- source:
--   Azarmehr–Behnezhad 2026, Metric TSP in Sublinear Time: Breaking Two Approximation, https://arxiv.org/abs/2611.04283, §9.2.2, p.40 (PDF p.42), 'τ = (σ/2) µ(G)'; standard (Schrijver, Combinatorial Optimization, §30.2).

import Mathlib
import Definitions.Def_GraphMatching_basic

namespace GraphMatching

/-- **Fractional vertex cover via the bipartite double cover.** Azarmehr, Behnezhad, *Metric TSP in Sublinear Time:
Breaking Two Approximation*, arXiv:2611.04283, §9.2.2, p.40 (PDF p.42): "Recall that G is the bipartite double cover,
and hence τ = (σ/2) µ(G)", where τ/σ is the minimum fractional vertex cover of the conflict graph. Twice the fractional
vertex cover number of a finite graph equals the matching number of its bipartite double cover. -/
theorem fracVC_eq {V : Type*} [Fintype V] (G : SimpleGraph V) :
    2 * fracVC G = (matchingNumber (doubleCover G) : ℝ) := by sorry

end GraphMatching
