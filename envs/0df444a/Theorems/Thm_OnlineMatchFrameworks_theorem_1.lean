-- Prove2me | Theorems.Thm_OnlineMatchFrameworks_theorem_1
-- name    : OnlineMatchFrameworks.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:32:10.362262+00:00
-- url     : https://prove2.me/theorems/17f55952-de4f-4ea1-ae74-4023ee080372
-- title:
--   Theorem 1: Algorithm 1 is $0.5\kappa$-competitive
-- statement:
--   Let $U$ be a finite set of offline items and $V$ a finite set of online customers, with edge probabilities $p_{u,v}\in[0,1]$, vertex weights $w_u\ge 0$ and a survival function $S$ for the patience. Let $\kappa\in[0,1]$ and let $\mathrm{BB}$ be a $\kappa$-approximate black box for the star problems. For every order in which the customers arrive, the expected reward of Algorithm 1 satisfies
--   $$
--   0.5\,\kappa\,\mathrm{OPT}(G)\le\mathrm{ALG}(G),
--   $$
--   where $\mathrm{OPT}(G)$ is the expected reward of the best offline sequential probing strategy.
--
--   This is the first guarantee of the paper's framework: any approximation for a single customer yields, at a loss of a factor $2$, a competitive online algorithm under adversarial arrivals.
--
--   Differences from the source:
--   - generalization: patience deterministic (p.11), an arbitrary distribution (§5.2) or item hazard rates (§5.1) → one survival function S_v(l) in [0,1], sublist monotone; reason: the three models satisfy the hypotheses (proved in the sanity file), so each is a special case
--   - generalization: the best sequential offline probing algorithm, finishing one vertex before the next (p.12) → supremum over decision trees that may choose the next customer adaptively; reason: a fixed order is a special case, so the benchmark can only be larger; randomized algorithms are mixtures of trees
--   - reading: expected size of the matching (p.14), while the setting, LP (1) and the proof use weight → expected weight, w ≥ 0; reason: size is w ≡ 1, so this is the stronger reading
--   - reading: StarBB within a factor κ of optimal (pp.5, 14), κ ∈ [0,1] → a PMF over duplicate-free lists of available items with κ·OPT(A,v) ≤ expected star value, for all A, v; reason: the form the proof on p.40 uses; the weight form on p.5 implies it, and a randomized star policy is a mixture of lists
--   - reading: the order of arrival is set by an adversary (p.11) → every duplicate-free list of all of V; reason: the adversary fixes the order in advance
--   - encoding: ALG(G)/OPT(G) ≥ 0.5κ → 0.5κ·OPT(G) ≤ ALG(G); reason: covers OPT(G) = 0 and is equivalent when OPT(G) > 0
-- source:
--   Brubach, Grammel, Ma & Srinivasan, Online Matching Frameworks under Stochastic Rewards, Product Ranking, and Unknown Patience, arXiv:1907.03963v6, Theorem 1, p.15

import Definitions.Def_OnlineMatchFrameworks_BlackBox
import Definitions.Def_OnlineMatchFrameworks_Offline

namespace OnlineMatchFrameworks

/-- **Theorem 1.** Brubach, Grammel, Ma & Srinivasan, *Online Matching Frameworks under Stochastic
Rewards, Product Ranking, and Unknown Patience*, arXiv:1907.03963v6, Theorem 1, p.15: "Given a
κ-approximate black box for solving star graphs, Algorithm 1 achieves a competitive ratio of 0.5κ;
that is, for any bipartite graph G, `ALG(G)/OPT(G) ≥ 0.5κ`." The arrival order is arbitrary: the
adversary of p.11 fixes it in advance.

**Formalization Note.** The ratio is written `0.5κ · OPT(G) ≤ ALG(G)`, which covers `OPT(G) = 0` and is
equivalent when `OPT(G) > 0`. The reward is weight (size is `w ≡ 1`). -/
theorem theorem_1 {U V : Type*} [DecidableEq U] [DecidableEq V] [Fintype U] [Fintype V]
    (G : Instance U V) (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (BB : Finset U → V → PMF (Policy U)) (hBB : G.IsKappaApprox κ BB)
    (order : List V) (hnd : order.Nodup) (hall : ∀ v, v ∈ order) :
    0.5 * κ * G.OPT ≤ G.ALG BB order := by sorry

end OnlineMatchFrameworks
