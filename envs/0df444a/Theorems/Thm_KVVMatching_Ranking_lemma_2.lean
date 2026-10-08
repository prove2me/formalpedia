-- Prove2me | Theorems.Thm_KVVMatching_Ranking_lemma_2
-- name    : KVVMatching.Ranking.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:41:44.644668+00:00
-- url     : https://prove2.me/theorems/ed046f26-d22e-4f79-b2ab-bc4251541712
-- title:
--   Lemma 2 — refusing arrivals cannot cover more girls
-- statement:
--   Fix a graph, an arrival order of boys, and a priority order of girls. A refusal algorithm may, at each arrival, either take its highest-ranked eligible girl or decline the boy even when an eligible girl exists. The refusal rule may depend on the time and that algorithm's current matching. Every girl matched by the refusal algorithm is also matched by RANKING under the same orders.
--
--   $$V(M_{\mathrm{refusal}})\subseteq V(M_{\mathrm{RANKING}}).$$
--
--   The comparison concerns the set of covered girls, not necessarily identical edges. It supports the comparison with EARLY and the triangular reduction.
-- source:
--   Karp, Vazirani, Vazirani, An Optimal Algorithm for On-line Bipartite Matching, STOC 1990, p. 354, refusal-algorithm paragraph and Lemma 2

import Definitions.Def_KVVMatching_Ranking_GreedyRun

namespace KVVMatching.Ranking

/-- Lemma 2, p. 354: an arbitrary refusal rule cannot cover more girls. -/
theorem lemma_2 {n : ℕ} (adj : Fin n → Fin n → Prop)
    (boyOrder girlRank : Equiv.Perm (Fin n))
    (refuse : ℕ → Finset (Fin n × Fin n) → Fin n → Bool) :
    ((greedyRun adj boyOrder girlRank refuse).image Prod.snd) ⊆
    ((greedyRun adj boyOrder girlRank (fun _ _ _ => false)).image Prod.snd) := by sorry

end KVVMatching.Ranking
