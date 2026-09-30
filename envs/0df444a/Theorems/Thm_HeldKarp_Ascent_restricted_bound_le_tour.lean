-- Prove2me | Theorems.Thm_HeldKarp_Ascent_restricted_bound_le_tour
-- name    : HeldKarp.Ascent.restricted_bound_le_tour
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T07:08:05.418491+00:00
-- url     : https://prove2.me/theorems/e41efe31-23b4-4423-b6f3-67c9bbb207d0
-- title:
--   §3: $w_{X,Y}(\pi)$ is a lower bound on every tour of the derived problem
-- statement:
--   Let $n \ge 3$, let $(c_{ij})$ be symmetric real edge weights on $K_n$, and let $X, Y$ be sets of edges of $K_n$. Let $T(X,Y)$ be the set of 1-trees that include every edge of $X$ and exclude every edge of $Y$, and
--   $$w_{X,Y}(\pi) = \min_{k \in T(X,Y)} [c_k + \pi\cdot v_k].$$
--   Then for every $\pi \in \mathbb R^n$ and every tour $H$ of the **derived problem** (a tour containing all edges of $X$ and no edge of $Y$),
--   $$w_{X,Y}(\pi) \le c(H).$$
--
--   This is the bound attached to each subproblem of the branch-and-bound procedure of §3, where the derived problem is obtained by forcing the edges of $X$ into and the edges of $Y$ out of the tour.
--
--   **Formalization Note** Edges are unordered pairs of vertices; "include $X$" is $X \subseteq E(G)$ and "exclude $Y$" is $Y \cap E(G) = \emptyset$. Since $H$ itself lies in $T(X,Y)$, the minimum is over a nonempty set. $n \ge 3$ is implicit.
-- source:
--   Held & Karp, The traveling-salesman problem and minimum spanning trees: Part II, Math. Programming 1 (1971), DOI 10.1007/BF01584070, §3, p. 14 (PDF p. 9), unnumbered

import Mathlib
import Definitions.Def_HeldKarp_Ascent_IsOneTree
import Definitions.Def_HeldKarp_Ascent_oneTreeBound

namespace HeldKarp.Ascent

/-- **The branch-and-bound lower bound** — Held & Karp, *The traveling-salesman problem and minimum
spanning trees: Part II*, Math. Programming 1 (1971), §3, p. 14 (PDF p. 9), unnumbered:
"let T(X, Y) be the set of all 1-trees which include the edges in X and exclude the edges in Y,
and let w_{X,Y}(π) = min_{k∈T(X,Y)} [c_k + π · v_k]. Then w_{X,Y}(π) is a lower bound on the cost
of any tour for the derived problem." The derived problem (same page) is the traveling-salesman
problem restricted to tours that include the edges in `X` and exclude the edges in `Y`.

Formalization Note: a tour `H` of the derived problem is a tour with `X ⊆ H.edgeSet` and
`Disjoint Y H.edgeSet`; its cost is its weight under the original weights `c`. For such `H` the
set `T(X, Y)` is nonempty, so the minimum is genuine. `3 ≤ n` is implicit in the paper. -/
theorem restricted_bound_le_tour {n : ℕ} [NeZero n] (hn : 3 ≤ n) (c : Sym2 (Fin n) → ℝ)
    (X Y : Set (Sym2 (Fin n))) (π : Fin n → ℝ) (H : SimpleGraph (Fin n)) (hH : IsTour H)
    (hX : X ⊆ H.edgeSet) (hY : Disjoint Y H.edgeSet) :
    restrictedBound c X Y π ≤ weight c H := by sorry

end HeldKarp.Ascent
