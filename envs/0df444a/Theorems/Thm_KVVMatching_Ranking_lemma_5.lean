-- Prove2me | Theorems.Thm_KVVMatching_Ranking_lemma_5
-- name    : KVVMatching.Ranking.lemma_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:52:25.112871+00:00
-- url     : https://prove2.me/theorems/57da2db8-14cc-4fc1-b13b-0bd5e6266dc6
-- title:
--   Lemma 5 — RANKING produces at least as large a matching as EARLY
-- statement:
--   Fix an upper-triangular $n\times n$ adjacency matrix with unit diagonal and any ordering of its rows. RANKING matches each arriving row to the highest-ranked eligible column. EARLY follows the same rule except that it refuses row $i$ when its own matching has already covered column $i$. For this fixed order,
--
--   $$|M_{\mathrm{EARLY}}(B,\sigma)|\le |M_{\mathrm{RANKING}}(B,\sigma)|.$$
--
--   This is a pointwise comparison for every row order, before taking any expectation.
-- source:
--   Karp, Vazirani, Vazirani, An Optimal Algorithm for On-line Bipartite Matching, STOC 1990, p. 354, EARLY definition and Lemma 5

import Definitions.Def_KVVMatching_Ranking_Algorithms

namespace KVVMatching.Ranking

/-- Lemma 5, p. 354: RANKING's matching is at least as large as EARLY's. -/
theorem lemma_5 {n : ℕ} (adj : Fin n → Fin n → Prop)
    (hdiag : ∀ i, adj i i)
    (hupper : ∀ i j, adj i j → i ≤ j)
    (rowOrder : Equiv.Perm (Fin n)) :
    (earlyMatching adj rowOrder).card ≤ (rowRankingMatching adj rowOrder).card := by sorry

end KVVMatching.Ranking
