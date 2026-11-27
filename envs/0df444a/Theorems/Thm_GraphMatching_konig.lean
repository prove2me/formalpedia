-- Prove2me | Theorems.Thm_GraphMatching_konig
-- name    : GraphMatching.konig
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T04:25:40.111797+00:00
-- url     : https://prove2.me/theorems/cfd2c5d0-6ce1-4103-99f5-9a6cf98e2167
-- title:
--   König's theorem: $\tau(H)=\nu(H)$ for bipartite $H$
-- statement:
--   Let $H$ be a finite simple graph on the vertex set $\{0,1\}\times V$ whose edges all join a vertex of $\{0\}\times V$ to a vertex of $\{1\}\times V$ (so $H$ is bipartite with these two sides). Then the minimum size of a vertex cover equals the maximum size of a matching:
--   $$\tau(H)=\nu(H).$$
--
--   This is König's minimax theorem for bipartite graphs. Applied to the bipartite double cover of a conflict graph it identifies the matching number of the double cover with its vertex cover number, which is twice the fractional vertex cover number of the conflict graph.
--
--   **Formalization Note** Every bipartite graph with a given bipartition can be written on a type of the form `Bool × V` by padding the smaller side; the statement uses this form.
-- source:
--   D. Kőnig 1931; A. Schrijver, Combinatorial Optimization (2003), Theorem 16.2. Used in Azarmehr–Behnezhad 2026, https://arxiv.org/abs/2611.04283, §9.2.2, p.38–41.

import Mathlib
import Definitions.Def_GraphMatching_basic

namespace GraphMatching

/-- **König's theorem** (D. Kőnig, 1931; Schrijver, *Combinatorial Optimization*, Thm 16.2). In a bipartite graph the
minimum size of a vertex cover equals the maximum size of a matching. The bipartition is given by the first
coordinate of the vertex type `Bool × V`. -/
theorem konig {V : Type*} [Fintype V] (H : SimpleGraph (Bool × V))
    (hH : ∀ a u b v, H.Adj (a, u) (b, v) → a ≠ b) :
    vcNumber H = matchingNumber H := by sorry

end GraphMatching
