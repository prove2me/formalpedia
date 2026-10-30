-- Prove2me | Theorems.Thm_OfflineStochMatchFull_InfinitePatience_lemma_1
-- name    : OfflineStochMatchFull.InfinitePatience.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T13:48:12.575063+00:00
-- url     : https://prove2.me/theorems/f03819d6-b95a-442a-a132-1723d1883395
-- title:
--   Lemma 1 — LP upper bound for all adaptive probing policies
-- statement:
--   Let $G=(V,E)$ be a finite loopless undirected graph, with independent hidden activation probabilities $p_e\in[0,1]$, nonnegative real weights $w_e$, and arbitrary integral or infinite patience bounds $t_v$. An admissible policy may stop at any history or choose a new legal probe using arbitrary randomization based on all previous probes and outcomes. Active probes must be matched immediately. Write $R(\pi)$ for the expected terminal matched weight under this execution, $\mathrm{OPT}$ for its supremum over all admissible policies, and $\mathrm{LP}$ for the optimum of LP (3).
--
--   Both optimization values are well defined and attained. Every feasible LP value and every policy reward lies in $[0,\sum_e w_e]$, and
--
--   $$
--   R(\pi)\le\mathrm{LP}\quad(\pi\in\Pi),\qquad
--   \mathrm{OPT}\le\mathrm{LP}.
--   $$
--
--   The LP upper bound supports approximation comparisons against the entire adaptive policy class, rather than a restricted order or a supplied benchmark. Patiences $0$, $1$ and $\infty$, isolated vertices, empty graphs and zero probabilities are included.
--
--   **Formalization Note** The optimization values are computed independently from feasible LP objectives and actual policy execution rewards. Their nonemptiness, boundedness and attainment are conclusions, never hypotheses. The normalized action kernels and finite execution horizon do not restrict adaptive private randomization.
--
--   Differences from the source:
--   - generalization: the source graph has edges that are unordered pairs of distinct vertices → the reused loopless graph interface also permits parallel edges; reason: every finite simple source graph embeds by an injective endpoint map; the stated bounds also hold for distinct parallel edge labels
--   - generalization: the expected weight of any optimal probing algorithm is at most LP → the expected weight of every admissible adaptive randomized probing policy and their attained optimum is at most LP; reason: an optimum dominates every admissible policy, so the all-policy form includes the printed optimal-policy comparison
--   - encoding: adaptive randomized probe-commit algorithms with arbitrary independent internal randomness → normalized PMFs on next-edge-or-stop actions at observable probe histories, with the induced finite execution expectation; reason: conditional action distributions represent every admissible randomized policy; no edge repeats and all runs have at most |E| probes
--   - encoding: optimal objective LP and an optimal probing algorithm → real suprema of feasible LP and actual policy rewards, with nonemptiness, boundedness, and attainment asserted as conclusions; reason: the source finite problem has a feasible zero LP vector and a legal stopping policy; these conclusions exclude default suprema without assuming the comparison theorem
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3 (20 April 2026), https://arxiv.org/abs/2106.06892v3, §2, Lemma 1 (Bansal et al. [7]), p. 7; standing probe-commit and patience model §§1–2 pp. 1–2, 6–7.

import Mathlib
import Definitions.Def_OfflineStochMatchFull_InfinitePatience_Values

namespace OfflineStochMatchFull.InfinitePatience

/-- Lemma 1 (Bansal et al. [7]), arXiv:2106.06892v3, §2, p. 7.
All legal adaptive randomized policies are bounded, at arbitrary integral/∞
patiences, including 0 and 1. Attainment and boundedness are conclusions. -/
theorem lemma_1 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (p w : E → ℝ) (t : V → ℕ∞)
    (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) (hw : ∀ e, 0 ≤ w e) :
    OptimaAttained G p t w ∧
    (∀ π : ProbingPolicy G t, policyReward G p t w π ≤ lpValue G p t w) ∧
    OPT G p t w ≤ lpValue G p t w := by sorry

end OfflineStochMatchFull.InfinitePatience
