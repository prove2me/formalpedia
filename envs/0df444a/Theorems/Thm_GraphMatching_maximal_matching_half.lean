-- Prove2me | Theorems.Thm_GraphMatching_maximal_matching_half
-- name    : GraphMatching.maximal_matching_half
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T04:25:36.197736+00:00
-- url     : https://prove2.me/theorems/c9316288-711c-40aa-bde8-9b4330b5ac1f
-- title:
--   A maximal matching has at least half the maximum size
-- statement:
--   Let $H$ be a finite simple graph and $M$ a maximal matching of $H$, i.e. a matching such that every edge of $H$ shares a vertex with some edge of $M$. Then
--   $$\nu(H)\le 2\,|M| .$$
--
--   This is the standard fact behind matching-size estimators that sample a random greedy maximal matching: its size is between $\nu(H)/2$ and $\nu(H)$.
--
--   **Formalization Note** The matching property of $M$ is part of the hypotheses; the proof only uses that the $2|M|$ endpoints of $M$ form a vertex cover.
-- source:
--   Standard; S. Behnezhad, Time-optimal sublinear algorithms for matching and vertex cover, FOCS 2021, cited as Lemma 9.9 in Azarmehr–Behnezhad 2026, https://arxiv.org/abs/2611.04283, §9.2.2, p.40.

import Mathlib
import Definitions.Def_GraphMatching_basic

namespace GraphMatching

/-- **Maximal matchings are 2-approximate.** Behnezhad, FOCS 2021 (cited as Lemma 9.9 in Azarmehr–Behnezhad,
arXiv:2611.04283, p.40): the randomized greedy maximal matching "2-approximates the maximum matching size". Any matching
`M` that meets every edge of `H` satisfies `ν(H) ≤ 2|M|`. -/
theorem maximal_matching_half {W : Type*} [Fintype W] (H : SimpleGraph W) (M : Finset (Sym2 W))
    (hM : IsMatching H M) (hmax : ∀ e ∈ H.edgeSet, ∃ f ∈ M, ∃ x, x ∈ e ∧ x ∈ f) :
    matchingNumber H ≤ 2 * M.card := by sorry

end GraphMatching
