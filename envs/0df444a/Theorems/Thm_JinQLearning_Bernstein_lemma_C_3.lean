-- Prove2me | Theorems.Thm_JinQLearning_Bernstein_lemma_C_3
-- name    : JinQLearning.Bernstein.lemma_C_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:37:22.370655+00:00
-- url     : https://prove2.me/theorems/1074887d-e073-473c-916c-994b12f370c2
-- title:
--   Lemma C.3 — variance comparison
-- statement:
--   For each fixed positive numerical c2 there is c>0 independent of all instance parameters and c1. For any positive c1, p in (0,1) and each episode k, with probability at least 1-p/K the following implication holds: if printed (C.4) holds and every Q_h^{k'}(x,a)-Q_h^star(x,a)>=0 for every k'<k and all states, actions and stages, then simultaneously for all (x,a,h), with t=N_h^k(x,a),
--   $$|\mathbb V_hV_{h+1}^\star(x,a)-W_t(x,a,h)|\le c\left(\frac{SA\sqrt{H^7\iota}}t+\sqrt{\frac{H^7SA\iota}t}\right).$$
--   The implication is inside the event, not a conditional probability given optimism. At t=0 the radius is infinite.
--
--   Differences from the source:
--   - encoding: finite nonempty state/action sets and one-based stages and episodes → Fin S, Fin A, Fin H, Fin K with NeZero instances and zero-based indices; reason: finite relabeling preserves every positive cardinality, horizon and episode count; index h represents source stage h+1
--   - encoding: stage-dependent transitions and rewards in [0,1] → the published nonstationary MDP with a common action set via equivalences, reward equal to negative cost, and the [0,1] reward bounds; reason: cost/reward sign conversion and action relabeling are exact; arbitrary real transition rows remain independent across stages, and unused stages beyond H are unrestricted
--   - encoding: conditional expected policy values and optimal values → finite backward recursions with terminal zero and nonempty finite maxima; reason: these construct the Bellman values on precisely the finite-horizon model without assuming value equations
--   - encoding: N, mu, sigma and previous beta stored for each triple → chronological lists of observed next-stage values, with N=length, mu=sum, sigma=sum of squares and beta computed from the list; reason: the same historical values give exactly the stated accumulators and updates; no claim about the storage complexity of the encoding is made
--   - reading: Theorem 2 invokes (C.3) but Algorithm 2 line 10 has (sigma-mu^2)/t → use the explicit (C.1)-(C.3) centered variance sigma/t-(mu/t)^2 and beta_0=0; reason: the theorem explicitly specifies these equations; the contradictory pseudocode is recorded in insight I1
--   - encoding: probability over adaptive episodes and arbitrary initial states → finite sums of conditional start-law, greedy-policy-law and transition probability products, all with arbitrary real probabilities; reason: every nonanticipating randomized start rule is a kernel on the finite past; deterministic choices are point masses, and fresh transitions use their stated conditional rows
--   - generalization: an unspecified greedy Markov-policy tie selection before each episode → arbitrary randomized kernels over greedy Markov policies given past history and the initial state; reason: deterministic tie selections are point masses; conditioning on a selected policy gives exactly the source episode dynamics
--   - encoding: absolute constants and O notation → positive existential real constants before all cardinalities, models, confidence parameters and adaptive rules; reason: this is the uniform finite-time interpretation; no numerical constant or asymptotic threshold is invented
--   - encoding: singular analytical radii at zero visits → the bound is nonrestrictive at zero visits, written as a positive-count implication; W_0=0 and beta_0=0; reason: this encodes an infinite radius without real division by zero; positive counts use the exact source formulas, and C.1/C.4 retain their initialization cases
--   - encoding: visits k_1,...,k_t with weights alpha_t^i → a masked sum over previous episode indices j with visit rank N_h^j(x,a)+1; reason: each earlier visit occurs once and the chronological rank is exactly i
--   - reading: the development fixes universal bonus constants → C.3 and C.7 quantify a fixed positive c2 first, then a bound constant, both before every problem parameter; c1 is arbitrary positive; reason: the implicit constants may depend on the already fixed numerical bonus constant, but never on the MDP, history, horizon, weights or confidence level
-- source:
--   Jin, Allen-Zhu, Bubeck & Jordan, Is Q-learning Provably Efficient?, arXiv:1807.03765v1, p. 16, Lemma C.3.

import Definitions.Def_JinQLearning_Bernstein_Statistics

open scoped BigOperators

namespace JinQLearning.Bernstein

theorem lemma_C_3 :
    ∀ c₂ : ℝ, 0 < c₂ → ∃ c : ℝ, 0 < c ∧ ∀ c₁ : ℝ, 0 < c₁ →
    ∀ (S A H K : ℕ) [NeZero S] [NeZero A] [NeZero H] [NeZero K],
    ∀ (M : Model S A H) (p : ℝ), 0 < p → p < 1 →
    ∀ (start : StartRule S A H) (tie : TieRule S A H),
    ∀ k : Fin K,
    let ℓ := iota S A H K p
    1 - p / K ≤ probability (K := K) M c₁ c₂ ℓ start tie (fun ω =>
      (CoarseBound M c₁ c₂ ℓ ω ∧
        ∀ (j : Fin K), j.val < k.val → ∀ (h : Fin H) (x : Fin S) (a : Fin A),
          0 ≤ (snapshot M c₁ c₂ ℓ ω j.val).Q h x a - optimalQ M h x a) →
      ∀ (h : Fin H) (x : Fin S) (a : Fin A),
        let ys := (snapshot M c₁ c₂ ℓ ω k.val).observations h x a
        0 < ys.length →
        |variance M h x a (optimalValue M (h.val + 1)) - empiricalVariance ys| ≤
          c * varianceRadius S A H ℓ ys.length) := by sorry

end JinQLearning.Bernstein
