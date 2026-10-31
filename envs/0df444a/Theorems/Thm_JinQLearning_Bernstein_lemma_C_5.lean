-- Prove2me | Theorems.Thm_JinQLearning_Bernstein_lemma_C_5
-- name    : JinQLearning.Bernstein.lemma_C_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:37:08.385986+00:00
-- url     : https://prove2.me/theorems/e8390ec1-62fc-432e-86f0-e82e3154915e
-- title:
--   Lemma C.5 — cumulative conditional variance
-- statement:
--   There is an absolute positive constant c such that for every positive choice of bonus constants, every finite episodic instance and p in (0,1), with probability at least 1-p,
--   $$\sum_{k=1}^K\sum_{h=1}^H\mathbb V_h V_{h+1}^{\pi_k}(x_h^k,a_h^k)\le c(HT+H^3\iota),\qquad T=KH.$$
--   The values are those of the actual greedy Markov policies selected before each episode, with all randomized nonanticipating starts and tie selections allowed. No good-event hypothesis is imposed.
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
--   Jin, Allen-Zhu, Bubeck & Jordan, Is Q-learning Provably Efficient?, arXiv:1807.03765v1, p. 19, Lemma C.5.

import Definitions.Def_JinQLearning_Bernstein_Statistics

open scoped BigOperators

namespace JinQLearning.Bernstein

theorem lemma_C_5 :
    ∃ c : ℝ, 0 < c ∧ ∀ c₁ c₂ : ℝ, 0 < c₁ → 0 < c₂ →
    ∀ (S A H K : ℕ) [NeZero S] [NeZero A] [NeZero H] [NeZero K],
    ∀ (M : Model S A H) (p : ℝ), 0 < p → p < 1 →
    ∀ (start : StartRule S A H) (tie : TieRule S A H),
    let ℓ := iota S A H K p
    1 - p ≤ probability (K := K) M c₁ c₂ ℓ start tie (fun ω =>
      ∑ k : Fin K, ∑ h : Fin H,
        variance M h ((ω k).2 h.castSucc) (episodeAction (ω k) h)
          (policyValue M (ω k).1 (h.val + 1)) ≤
        c * ((H : ℝ) * (K * H) + (H : ℝ) ^ 3 * ℓ)) := by sorry

end JinQLearning.Bernstein
