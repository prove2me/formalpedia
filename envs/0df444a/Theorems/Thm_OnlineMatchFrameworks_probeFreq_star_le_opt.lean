-- Prove2me | Theorems.Thm_OnlineMatchFrameworks_probeFreq_star_le_opt
-- name    : OnlineMatchFrameworks.probeFreq_star_le_opt
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:31:54.450386+00:00
-- url     : https://prove2.me/theorems/e73b4eb8-4d60-4070-b364-e33e53b0be60
-- title:
--   Proof of Lemma 1: offline probe frequencies satisfy (1d)
-- statement:
--   Let $T$ be an offline strategy valid from all items and customers, with probe frequencies $x^T$. For every $U'\subseteq U$ and every customer $v$,
--   $$
--   \sum_{u\in U'}x^T_{u,v}p_{u,v}w_u\le\mathrm{OPT}(U',v).
--   $$
--   This is the new constraint of LP (1), which tightens the LP against the single-customer optimum.
--
--   Differences from the source:
--   - generalization: patience deterministic (p.11), an arbitrary distribution (§5.2) or item hazard rates (§5.1) → one survival function S_v(l) in [0,1], sublist monotone; reason: the three models satisfy the hypotheses (proved in the sanity file), so each is a special case
--   - generalization: the best sequential offline probing algorithm, finishing one vertex before the next (p.12) → supremum over decision trees that may choose the next customer adaptively; reason: a fixed order is a special case, so the benchmark can only be larger; randomized algorithms are mixtures of trees
--   - encoding: x_{u,v} is the probability that the strategy probes (u,v) → the recursion probeFreq over the tree; reason: total expectation over the tree
--   - generalization: x_{u,v} the probe probabilities of an adaptive offline algorithm which is optimal (p.39) → the probe frequencies of every strategy valid from all items and customers; reason: the optimal strategy is one valid strategy, so it is a special case
-- source:
--   Brubach, Grammel, Ma & Srinivasan, Online Matching Frameworks under Stochastic Rewards, Product Ranking, and Unknown Patience, arXiv:1907.03963v6, Appendix A, proof of Lemma 1, p.39, "the new constraint (1d) is satisfied by this assignment"

import Definitions.Def_OnlineMatchFrameworks_Offline
import Definitions.Def_OnlineMatchFrameworks_LP

open scoped BigOperators

namespace OnlineMatchFrameworks

/-- **Offline probe frequencies satisfy (1d).** arXiv:1907.03963v6, Appendix A, proof of Lemma 1, p.39,
"the new constraint (1d) is satisfied by this assignment".

**Formalization Note.** The simulation printed on p.39 does not reproduce patience feedback under
stochastic patience, but the inequality still holds through restricting each list to `U'`; that uses
`Instance.surv_mono`. -/
theorem probeFreq_star_le_opt {U V : Type*} [DecidableEq U] [DecidableEq V] [Fintype U] [Fintype V]
    (G : Instance U V) (T : Strategy U V) (hT : T.ValidFrom Finset.univ Finset.univ)
    (U' : Finset U) (v : V) :
    ∑ u ∈ U', G.probeFreq T u v * G.p u v * G.w u ≤ G.starOpt U' v := by sorry

end OnlineMatchFrameworks
