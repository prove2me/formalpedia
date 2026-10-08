-- Prove2me | Theorems.Thm_KVVMatching_Ranking_lemma_1
-- name    : KVVMatching.Ranking.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:41:36.90938+00:00
-- url     : https://prove2.me/theorems/18e6ed38-e33c-4e35-a14b-017e5c9641d5
-- title:
--   Lemma 1 — duality of RANKING
-- statement:
--   Fix a bipartite graph and an ordering of each side. Girls arriving in their order and selecting the highest-ranked available boy produce the same set of edges as boys arriving in their priority order and selecting the highest-ranked eligible girl, where the girls' priority order is their original arrival order.
--
--   $$M_{\mathrm{girls\ arrive}}(B;\sigma_V,\sigma_U)=M_{\mathrm{boys\ arrive}}(B;\sigma_U,\sigma_V).$$
--
--   This **duality principle** allows the analysis to exchange which side arrives online while retaining the individual matched edges.
--
--   **Formalization Note** Each permutation maps a time or priority index to a vertex; a smaller index arrives earlier or has higher priority. The two runs' edge pairs are placed in the same (boy, girl) orientation before comparison.
-- source:
--   Karp, Vazirani, Vazirani, An Optimal Algorithm for On-line Bipartite Matching, STOC 1990, p. 353, Duality Principle and Lemma 1

import Definitions.Def_KVVMatching_Ranking_GreedyRun

namespace KVVMatching.Ranking

/-- Lemma 1, p. 353: the duality principle for fixed orders. -/
theorem lemma_1 {n : ℕ} (adj : Fin n → Fin n → Prop)
    (boyOrder girlOrder : Equiv.Perm (Fin n)) :
    (greedyRun (fun g b => adj b g) girlOrder boyOrder
      (fun _ _ _ => false)).image Prod.swap =
    greedyRun adj boyOrder girlOrder (fun _ _ _ => false) := by sorry

end KVVMatching.Ranking
