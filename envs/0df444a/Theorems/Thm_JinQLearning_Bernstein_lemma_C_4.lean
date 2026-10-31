-- Prove2me | Theorems.Thm_JinQLearning_Bernstein_lemma_C_4
-- name    : JinQLearning.Bernstein.lemma_C_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:37:24.094529+00:00
-- url     : https://prove2.me/theorems/188c1a89-e760-47cc-89e2-ca73f495c979
-- title:
--   Lemma C.4 — optimism and fine bound
-- statement:
--   There are absolute c1,c2>0 such that, for every model and p in (0,1), the actual process with (C.2) satisfies, with probability at least 1-2p, simultaneously for every (x,a,h,k),
--   $$0\le (Q_h^k-Q_h^\star)(x,a)\le\alpha_t^0 H+\sum_{i=1}^t\alpha_t^i(V_{h+1}^{k_i}-V_{h+1}^\star)(x_{h+1}^{k_i})+\beta_t(x,a,h).$$
--   Here t=N_h^k(x,a) and k_i are exactly its previous visit episodes. Both bounds include t=0 with beta_0=0. No optimism or good event is assumed.
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
--   - encoding: visits k_1,...,k_t with weights alpha_t^i → a masked sum over previous episode indices j with visit rank N_h^j(x,a)+1; reason: each earlier visit occurs once and the chronological rank is exactly i
-- source:
--   Jin, Allen-Zhu, Bubeck & Jordan, Is Q-learning Provably Efficient?, arXiv:1807.03765v1, p. 18, Lemma C.4.

import Definitions.Def_JinQLearning_Bernstein_Statistics

open scoped BigOperators

namespace JinQLearning.Bernstein

theorem lemma_C_4 :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
    ∀ (S A H K : ℕ) [NeZero S] [NeZero A] [NeZero H] [NeZero K],
    ∀ (M : Model S A H) (p : ℝ), 0 < p → p < 1 →
    ∀ (start : StartRule S A H) (tie : TieRule S A H),
    let ℓ := iota S A H K p
    1 - 2 * p ≤ probability (K := K) M c₁ c₂ ℓ start tie (fun ω =>
      ∀ (k : Fin K) (h : Fin H) (x : Fin S) (a : Fin A),
        let q := snapshot M c₁ c₂ ℓ ω k.val
        0 ≤ q.Q h x a - optimalQ M h x a ∧
        q.Q h x a - optimalQ M h x a ≤ errorBase M c₁ c₂ ℓ ω k h x a +
          beta S A H c₁ c₂ ℓ (q.observations h x a)) := by sorry

end JinQLearning.Bernstein
