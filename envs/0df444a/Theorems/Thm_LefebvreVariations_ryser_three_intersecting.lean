-- Prove2me | Theorems.Thm_LefebvreVariations_ryser_three_intersecting
-- name    : LefebvreVariations.ryser_three_intersecting
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-24T22:06:11.694557+00:00
-- url     : https://prove2.me/theorems/199f359d-21ce-4160-8e8d-67998f4a8958
-- title:
--   Lefebvre's variations, No. 10 — on a theme by Ryser: Ryser's conjecture for intersecting 3-partite hypergraphs
-- statement:
--   This is the intersecting case of Ryser's conjecture for $3$-partite hypergraphs (Ten Challenges 08).
--
--   Let $H$ be a finite $3$-uniform $3$-partite hypergraph: its vertex set is split into three parts and every edge has exactly one vertex in each part. Suppose the edges of $H$ pairwise intersect, so that its matching number is at most $1$. Then $H$ has a vertex cover of size at most two:
--
--   $$
--   \tau(H)\ \le\ 2 .
--   $$
--
--   Ryser's conjecture asserts $\tau(H)\le (r-1)\,\nu(H)$ for every $r$-partite $r$-uniform hypergraph; for $r=3$ it is a theorem of Aharoni, and the statement above is its case $\nu(H)=1$ (when $H$ has no edge, $\tau(H)=0$). The intersecting case is the base configuration that the general argument for $r=3$ and the open cases $r\ge4$ build on.
--
--   **Formalization Note** The hypergraph, uniformity, partiteness and cover number are the mission's `FinHypergraph`, `IsUniform`, `IsPartite` and `coverNumber`. Pairwise intersection is stated directly on the edges; the empty hypergraph is allowed.
-- source:
--   Special case (matching number 1) of: R. Aharoni, Ryser's conjecture for tripartite 3-graphs, Combinatorica 21 (2001), no. 1, 1–4 (τ ≤ 2ν for every 3-partite 3-uniform hypergraph). Conjecture: H. J. Ryser (1971), as stated in J. R. Henderson, Permutation decompositions of (0,1)-matrices and decomposition transversals, PhD thesis, Caltech, 1971. Parent problem: TenChallenges.challenge_08 (Ryser's conjecture).

import Mathlib
import Definitions.Def_TenChallenges_Hypergraph

namespace LefebvreVariations

open FinHypergraph

/-- Ryser's conjecture (Challenge 08), `r = 3` and matching number `1`: a
3-uniform 3-partite hypergraph whose edges pairwise intersect has a vertex cover of
size at most `2 = (r-1)·ν` (with `ν = 0`, no edge, the cover number is `0`).
Source: Ryser's conjecture for intersecting hypergraphs, settled for `r = 3` by
Ryser himself and for `r = 4, 5` by Tuza, "Ryser's conjecture on transversals of
r-partite hypergraphs", Ars Combin. 8 (1979), 63-68 (the case `r = 3` for all `ν`
is Aharoni 2001). -/
theorem ryser_three_intersecting {V : Type*} [DecidableEq V] (H : FinHypergraph V)
    (hu : H.IsUniform 3) (hp : H.IsPartite 3)
    (hint : ∀ e ∈ H.edges, ∀ f ∈ H.edges, (e ∩ f).Nonempty) :
    H.coverNumber ≤ 2 := by
  sorry

end LefebvreVariations
