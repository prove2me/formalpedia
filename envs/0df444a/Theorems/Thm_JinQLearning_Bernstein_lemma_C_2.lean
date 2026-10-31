-- Prove2me | Theorems.Thm_JinQLearning_Bernstein_lemma_C_2
-- name    : JinQLearning.Bernstein.lemma_C_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:37:23.047027+00:00
-- url     : https://prove2.me/theorems/fab6d5d9-1aa2-492f-9127-3f1d57833d3d
-- title:
--   Lemma C.2 — coarse bound on Q minus optimal Q (as printed)
-- statement:
--   There is an absolute c2>0 such that for every c1>0, every finite episodic model and every p in (0,1), the actual process with beta from (C.2) satisfies the following simultaneously with probability at least 1-p. For every (x,a,h,k), with t=N_h^k(x,a) and previous visits k_i,
--   $$ (V_h^k-V_h^\star)(x_h^k)\le\alpha_t^0 H+\sum_{i=1}^t\alpha_t^i(V_{h+1}^{k_i}-V_{h+1}^\star)(x_{h+1}^{k_i})+4c_2\sqrt{H^3\iota/t}. $$
--   The cap beta_t<=c2 sqrt(H^3 iota/t) is automatic from (C.2). The left side remains at the visited state even when (x,a) is unrelated; the printed false claim is retained (insight I2). Zero-count singular radii are infinite.
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
-- source:
--   Jin, Allen-Zhu, Bubeck & Jordan, Is Q-learning Provably Efficient?, arXiv:1807.03765v1, p. 16, Lemma C.2.

import Definitions.Def_JinQLearning_Bernstein_Statistics

open scoped BigOperators

namespace JinQLearning.Bernstein

theorem lemma_C_2 :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ c₁ : ℝ, 0 < c₁ →
    ∀ (S A H K : ℕ) [NeZero S] [NeZero A] [NeZero H] [NeZero K],
    ∀ (M : Model S A H) (p : ℝ), 0 < p → p < 1 →
    ∀ (start : StartRule S A H) (tie : TieRule S A H),
    1 - p ≤ probability (K := K) M c₁ c₂ (iota S A H K p) start tie
      (fun ω => CoarseBound M c₁ c₂ (iota S A H K p) ω) := by sorry

end JinQLearning.Bernstein
