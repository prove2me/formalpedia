-- Prove2me | Theorems.Thm_JinQLearning_Bernstein_lemma_C_7
-- name    : JinQLearning.Bernstein.lemma_C_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:36:45.067625+00:00
-- url     : https://prove2.me/theorems/ee3e5ea9-524b-453e-9fa0-a9585adada78
-- title:
--   Lemma C.7 — weighted value error (as printed)
-- statement:
--   For each fixed positive numerical c2 there is a positive constant C, independent of all instance parameters, c1, weights and trajectories, such that the following holds. For any positive c1, finite episodic instance, p in (0,1) and replayed greedy path satisfying printed (C.4), every stage h and nonnegative real weight vector w of length K satisfy
--   $$\sum_{k=1}^K w_k\phi_h^k\le C\left(SA\|w\|_\infty\sqrt{H^5\iota}+\sqrt{SA\|w\|_1\|w\|_\infty H^5\iota}\right).$$
--   Here phi is (V_h^k-V_h^star)(x_h^k), the one-norm is the sum of the nonnegative weights and the infinity-norm is their maximum. Weights may be zero or chosen after observing the entire path. There is no optimism hypothesis. Insight I5 records a small-logarithm counterexample without changing this target.
--
--   Differences from the source:
--   - encoding: finite nonempty state/action sets and one-based stages and episodes → Fin S, Fin A, Fin H, Fin K with NeZero instances and zero-based indices; reason: finite relabeling preserves every positive cardinality, horizon and episode count; index h represents source stage h+1
--   - encoding: stage-dependent transitions and rewards in [0,1] → the published nonstationary MDP with a common action set via equivalences, reward equal to negative cost, and the [0,1] reward bounds; reason: cost/reward sign conversion and action relabeling are exact; arbitrary real transition rows remain independent across stages, and unused stages beyond H are unrestricted
--   - encoding: conditional expected policy values and optimal values → finite backward recursions with terminal zero and nonempty finite maxima; reason: these construct the Bellman values on precisely the finite-horizon model without assuming value equations
--   - encoding: N, mu, sigma and previous beta stored for each triple → chronological lists of observed next-stage values, with N=length, mu=sum, sigma=sum of squares and beta computed from the list; reason: the same historical values give exactly the stated accumulators and updates; no claim about the storage complexity of the encoding is made
--   - reading: Theorem 2 invokes (C.3) but Algorithm 2 line 10 has (sigma-mu^2)/t → use the explicit (C.1)-(C.3) centered variance sigma/t-(mu/t)^2 and beta_0=0; reason: the theorem explicitly specifies these equations; the contradictory pseudocode is recorded in insight I1
--   - encoding: absolute constants and O notation → positive existential real constants before all cardinalities, models, confidence parameters and adaptive rules; reason: this is the uniform finite-time interpretation; no numerical constant or asymptotic threshold is invented
--   - encoding: singular analytical radii at zero visits → the bound is nonrestrictive at zero visits, written as a positive-count implication; W_0=0 and beta_0=0; reason: this encodes an infinite radius without real division by zero; positive counts use the exact source formulas, and C.1/C.4 retain their initialization cases
--   - encoding: visits k_1,...,k_t with weights alpha_t^i → a masked sum over previous episode indices j with visit rank N_h^j(x,a)+1; reason: each earlier visit occurs once and the chronological rank is exactly i
--   - reading: the development fixes universal bonus constants → C.3 and C.7 quantify a fixed positive c2 first, then a bound constant, both before every problem parameter; c1 is arbitrary positive; reason: the implicit constants may depend on the already fixed numerical bonus constant, but never on the MDP, history, horizon, weights or confidence level
--   - reading: w=(w_1,...,w_k) followed by sums through K → a vector indexed by all K episodes; reason: the sum and proof identify the lower-case k in the vector length as K
--   - generalization: the weighted bound on a generated greedy Q-learning run satisfying (C.4) → the same implication for every replayed greedy policy/outcome path, including paths with zero transition mass; reason: every generated run is a greedy replay; the pathwise implication retains (C.4) and adds no condition on any source instance
-- source:
--   Jin, Allen-Zhu, Bubeck & Jordan, Is Q-learning Provably Efficient?, arXiv:1807.03765v1, pp. 21–22, Lemma C.7.

import Definitions.Def_JinQLearning_Bernstein_Statistics

open scoped BigOperators

namespace JinQLearning.Bernstein

theorem lemma_C_7 :
    ∀ c₂ : ℝ, 0 < c₂ → ∃ C : ℝ, 0 < C ∧ ∀ c₁ : ℝ, 0 < c₁ →
    ∀ (S A H K : ℕ) [NeZero S] [NeZero A] [NeZero H] [NeZero K],
    ∀ (M : Model S A H) (p : ℝ), 0 < p → p < 1 →
    ∀ (ω : Path S A H K),
    GreedyPath M c₁ c₂ (iota S A H K p) ω →
    CoarseBound M c₁ c₂ (iota S A H K p) ω →
    ∀ (h : Fin H) (w : Fin K → ℝ), (∀ k, 0 ≤ w k) →
      ∑ k, w k * phi M c₁ c₂ (iota S A H K p) ω k h ≤
        C * ((S : ℝ) * A * (Finset.univ.sup' Finset.univ_nonempty w) *
          Real.sqrt ((H : ℝ) ^ 5 * iota S A H K p) +
          Real.sqrt ((S : ℝ) * A * (∑ k, w k) *
            (Finset.univ.sup' Finset.univ_nonempty w) * (H : ℝ) ^ 5 * iota S A H K p)) := by sorry

end JinQLearning.Bernstein
