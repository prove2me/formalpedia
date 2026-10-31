-- Prove2me | Theorems.Thm_JinQLearning_Bernstein_theorem_2
-- name    : JinQLearning.Bernstein.theorem_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:37:13.387686+00:00
-- url     : https://prove2.me/theorems/437cfd54-407a-4457-ab66-9d1f2f97f016
-- title:
--   Theorem 2 — UCB-Bernstein Q-learning regret
-- statement:
--   There exist universal positive numerical constants c1,c2,C, before the model, cardinalities, horizon, episode count, confidence parameter and adaptive choices, with the following property. For every nonempty finite state/action space, positive H,K, stage-dependent real transition rows, deterministic rewards in [0,1], p in (0,1), arbitrary nonanticipating randomized initial-state rule and greedy policy tie selections, run the concrete Q-learning updates with (C.1)-(C.3). Set T=KH and iota=log(SAT/p). With probability at least 1-p, its pseudo-regret satisfies
--   $$R_K=\sum_{k=1}^K[V_1^\star(x_1^k)-V_1^{\pi_k}(x_1^k)]\le C\left(\sqrt{H^3SAT\iota}+\sqrt{H^9S^3A^3}\,\iota^2\right).$$
--   Both terms and their logarithms are retained for all positive horizons and episode counts. No stationary-transition, fixed-start, large-T, optimism or concentration assumption is added.
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
-- source:
--   Jin, Allen-Zhu, Bubeck & Jordan, Is Q-learning Provably Efficient?, arXiv:1807.03765v1, p. 15, Theorem 2 (restated).

import Definitions.Def_JinQLearning_Bernstein_Statistics

open scoped BigOperators

namespace JinQLearning.Bernstein

theorem theorem_2 :
    ∃ c₁ c₂ C : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 0 < C ∧
    ∀ (S A H K : ℕ) [NeZero S] [NeZero A] [NeZero H] [NeZero K],
    ∀ (M : Model S A H) (p : ℝ), 0 < p → p < 1 →
    ∀ (start : StartRule S A H) (tie : TieRule S A H),
    let ℓ := iota S A H K p
    1 - p ≤ probability (K := K) M c₁ c₂ ℓ start tie (fun ω =>
      regret M ω ≤ C * (Real.sqrt ((H : ℝ) ^ 3 * S * A * (K * H) * ℓ) +
        Real.sqrt ((H : ℝ) ^ 9 * (S : ℝ) ^ 3 * (A : ℝ) ^ 3) * ℓ ^ 2)) := by sorry

end JinQLearning.Bernstein
