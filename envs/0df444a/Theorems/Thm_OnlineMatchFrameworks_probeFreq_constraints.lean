-- Prove2me | Theorems.Thm_OnlineMatchFrameworks_probeFreq_constraints
-- name    : OnlineMatchFrameworks.probeFreq_constraints
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:31:48.710995+00:00
-- url     : https://prove2.me/theorems/d18661ca-fe21-494c-b0f3-9a76a1d306c9
-- title:
--   Proof of Lemma 1: offline probe frequencies satisfy (1a), (1b), (1c) and $0\le x\le 1$
-- statement:
--   Let $T$ be an offline strategy valid from all items and customers, with probe frequencies $x^T$, and let $E$ be a valid budget. Then for all $u\in U$ and $v\in V$,
--   $$
--   \sum_{v}x^T_{u,v}p_{u,v}\le 1,\qquad\sum_{u}x^T_{u,v}p_{u,v}\le 1,\qquad\sum_{u}x^T_{u,v}\le E_v,\qquad 0\le x^T_{u,v}\le 1 .
--   $$
--   These inequalities say that $x^T$ meets the classical constraints of LP (1), as the first half of the upper bound needs.
--
--   Differences from the source:
--   - generalization: patience deterministic (p.11), an arbitrary distribution (§5.2) or item hazard rates (§5.1) → one survival function S_v(l) in [0,1], sublist monotone; reason: the three models satisfy the hypotheses (proved in the sanity file), so each is a special case
--   - generalization: the best sequential offline probing algorithm, finishing one vertex before the next (p.12) → supremum over decision trees that may choose the next customer adaptively; reason: a fixed order is a special case, so the benchmark can only be larger; randomized algorithms are mixtures of trees
--   - generalization: right side E[θ_v] of (1c) → a budget E_v in [0,∞] bounding the expected probes of every list; reason: E[θ_v] qualifies (proved in the sanity file) and specializes the statement
--   - encoding: x_{u,v} is the probability that the strategy probes (u,v) → the recursion probeFreq over the tree; reason: total expectation over the tree
--   - generalization: x_{u,v} the probe probabilities of an adaptive offline algorithm which is optimal (p.39) → the probe frequencies of every strategy valid from all items and customers; reason: the optimal strategy is one valid strategy, so it is a special case
-- source:
--   Brubach, Grammel, Ma & Srinivasan, Online Matching Frameworks under Stochastic Rewards, Product Ranking, and Unknown Patience, arXiv:1907.03963v6, Appendix A, proof of Lemma 1, p.39, "this assignment satisfies constraints (1a) and (1b)"

import Definitions.Def_OnlineMatchFrameworks_Offline
import Definitions.Def_OnlineMatchFrameworks_LP

open scoped BigOperators ENNReal

namespace OnlineMatchFrameworks

/-- **Offline probe frequencies satisfy (1a), (1b), (1c) and `0 ≤ x ≤ 1`.** arXiv:1907.03963v6,
Appendix A, proof of Lemma 1, p.39, "this assignment satisfies constraints (1a) and (1b)". -/
theorem probeFreq_constraints {U V : Type*} [DecidableEq U] [DecidableEq V] [Fintype U] [Fintype V]
    (G : Instance U V) (E : V → ℝ≥0∞) (hE : G.ValidBudget E) (T : Strategy U V)
    (hT : T.ValidFrom Finset.univ Finset.univ) :
    (∀ u, ∑ v, G.probeFreq T u v * G.p u v ≤ 1) ∧
      (∀ v, ∑ u, G.probeFreq T u v * G.p u v ≤ 1) ∧
      (∀ v, ENNReal.ofReal (∑ u, G.probeFreq T u v) ≤ E v) ∧
      (∀ u v, 0 ≤ G.probeFreq T u v ∧ G.probeFreq T u v ≤ 1) := by sorry

end OnlineMatchFrameworks
