-- Prove2me | Theorems.Thm_OnlineMatchFrameworks_lemma_1
-- name    : OnlineMatchFrameworks.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:31:41.865381+00:00
-- url     : https://prove2.me/theorems/5124d5f3-3ef7-4dde-baf6-3edf606af683
-- title:
--   Lemma 1: $\mathrm{OPT}_{\mathrm{LP}}(G)\ge\mathrm{OPT}(G)$
-- statement:
--   For every instance $G$ and every valid budget $E$,
--   $$
--   \mathrm{OPT}(G)\le\mathrm{OPT}_{\mathrm{LP}}(G).
--   $$
--   So LP (1) is an upper bound on the offline benchmark, which is what lets the algorithm be compared with the LP.
--
--   Differences from the source:
--   - generalization: patience deterministic (p.11), an arbitrary distribution (§5.2) or item hazard rates (§5.1) → one survival function S_v(l) in [0,1], sublist monotone; reason: the three models satisfy the hypotheses (proved in the sanity file), so each is a special case
--   - generalization: the best sequential offline probing algorithm, finishing one vertex before the next (p.12) → supremum over decision trees that may choose the next customer adaptively; reason: a fixed order is a special case, so the benchmark can only be larger; randomized algorithms are mixtures of trees
--   - reading: expected size of the matching (p.14), while the setting, LP (1) and the proof use weight → expected weight, w ≥ 0; reason: size is w ≡ 1, so this is the stronger reading
--   - generalization: right side E[θ_v] of (1c) → a budget E_v in [0,∞] bounding the expected probes of every list; reason: E[θ_v] qualifies (proved in the sanity file) and specializes the statement
-- source:
--   Brubach, Grammel, Ma & Srinivasan, Online Matching Frameworks under Stochastic Rewards, Product Ranking, and Unknown Patience, arXiv:1907.03963v6, Lemma 1, p.15

import Definitions.Def_OnlineMatchFrameworks_Offline
import Definitions.Def_OnlineMatchFrameworks_LP

open scoped ENNReal

namespace OnlineMatchFrameworks

/-- **Lemma 1.** arXiv:1907.03963v6, Lemma 1, p.15: "For any bipartite graph G,
`OPT_LP(G) ≥ OPT(G)`", for every budget valid for (1c), including `E[θ_v]`. -/
theorem lemma_1 {U V : Type*} [DecidableEq U] [DecidableEq V] [Fintype U] [Fintype V]
    (G : Instance U V) (E : V → ℝ≥0∞) (hE : G.ValidBudget E) :
    G.OPT ≤ G.OPTLP E := by sorry

end OnlineMatchFrameworks
