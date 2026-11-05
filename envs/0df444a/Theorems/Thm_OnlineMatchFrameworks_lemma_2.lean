-- Prove2me | Theorems.Thm_OnlineMatchFrameworks_lemma_2
-- name    : OnlineMatchFrameworks.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:31:55.1607+00:00
-- url     : https://prove2.me/theorems/d9424b87-5304-4d26-99b0-c24bf029439c
-- title:
--   Lemma 2: $\mathrm{ALG}(G)\ge0.5\kappa\,\mathrm{OPT}_{\mathrm{LP}}(G)$
-- statement:
--   For every instance $G$, every $\kappa\in[0,1]$, every $\kappa$-approximate black box, every budget $E$ and every arrival order,
--   $$
--   0.5\,\kappa\,\mathrm{OPT}_{\mathrm{LP}}(G)\le\mathrm{ALG}(G).
--   $$
--   So the greedy algorithm earns a constant fraction of the LP value, even when (1c) is dropped.
--
--   Differences from the source:
--   - generalization: patience deterministic (p.11), an arbitrary distribution (§5.2) or item hazard rates (§5.1) → one survival function S_v(l) in [0,1], sublist monotone; reason: the three models satisfy the hypotheses (proved in the sanity file), so each is a special case
--   - generalization: right side E[θ_v] of (1c) → any budget E_v in [0,∞]; reason: a larger feasible set only strengthens the lower bound on ALG, and E[θ_v] is one such budget
--   - reading: StarBB within a factor κ of optimal (pp.5, 14), κ ∈ [0,1] → a PMF over duplicate-free lists of available items with κ·OPT(A,v) ≤ expected star value, for all A, v; reason: the form the proof on p.40 uses; the weight form on p.5 implies it, and a randomized star policy is a mixture of lists
--   - reading: the order of arrival is set by an adversary (p.11) → every duplicate-free list of all of V; reason: the adversary fixes the order in advance
--   - reading: expected size of the matching (p.14), while the setting, LP (1) and the proof use weight → expected weight, w ≥ 0; reason: size is w ≡ 1, so this is the stronger reading
-- source:
--   Brubach, Grammel, Ma & Srinivasan, Online Matching Frameworks under Stochastic Rewards, Product Ranking, and Unknown Patience, arXiv:1907.03963v6, Lemma 2, p.15

import Definitions.Def_OnlineMatchFrameworks_BlackBox
import Definitions.Def_OnlineMatchFrameworks_LP

open scoped ENNReal

namespace OnlineMatchFrameworks

/-- **Lemma 2.** arXiv:1907.03963v6, Lemma 2, p.15: "If StarBB is a κ-approximate algorithm for star
graphs, then for any bipartite graph G, `ALG(G) ≥ 0.5κ OPT_LP(G)`", for every arrival order and any
budget `E` in (1c), even `E ≡ ⊤`. -/
theorem lemma_2 {U V : Type*} [DecidableEq U] [Fintype U] [Fintype V]
    (G : Instance U V) (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (BB : Finset U → V → PMF (Policy U)) (hBB : G.IsKappaApprox κ BB)
    (E : V → ℝ≥0∞) (order : List V) (hnd : order.Nodup) (hall : ∀ v, v ∈ order) :
    0.5 * κ * G.OPTLP E ≤ G.ALG BB order := by sorry

end OnlineMatchFrameworks
