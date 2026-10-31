-- Prove2me | Theorems.Thm_JinQLearning_Bernstein_lemma_C_6
-- name    : JinQLearning.Bernstein.lemma_C_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:37:10.170983+00:00
-- url     : https://prove2.me/theorems/ff2b2ce1-8ef2-421f-a43d-81f92a53eda4
-- title:
--   Lemma C.6 — empirical versus played-policy variance (as printed)
-- statement:
--   There are absolute c1,c2,c>0 such that for every finite episodic instance and p in (0,1), with probability at least 1-4p, simultaneously for every (k,h), put (x,a)=(x_h^k,a_h^k) and t=N_h^k(x,a). Then
--   $$W_t(x,a,h)\le\mathbb V_h V_{h+1}^{\pi_k}(x,a)+2H(\delta_{h+1}^k+\xi_{h+1}^k)+c\left(\frac{SA\sqrt{H^7\iota}}t+\sqrt{\frac{SAH^7\iota}t}\right).$$
--   The printed definitions are delta=(V^star_{h+1}-V^k_{h+1})(x^k_{h+1}) and xi=[(P_h-P_hat_h^k)(V^star_{h+1}-V^k_{h+1})](x_h^k,a_h^k). They are retained despite the proof gap in I3. Zero-count singular radii are infinite.
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
--   - reading: for all (k,h), with probability at least 1-4p → one event holding simultaneously for all (k,h); reason: the main proof sums these bounds on the same event
-- source:
--   Jin, Allen-Zhu, Bubeck & Jordan, Is Q-learning Provably Efficient?, arXiv:1807.03765v1, p. 20, Lemma C.6.

import Definitions.Def_JinQLearning_Bernstein_Statistics

open scoped BigOperators

namespace JinQLearning.Bernstein

theorem lemma_C_6 :
    ∃ c₁ c₂ c : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 0 < c ∧
    ∀ (S A H K : ℕ) [NeZero S] [NeZero A] [NeZero H] [NeZero K],
    ∀ (M : Model S A H) (p : ℝ), 0 < p → p < 1 →
    ∀ (start : StartRule S A H) (tie : TieRule S A H),
    let ℓ := iota S A H K p
    1 - 4 * p ≤ probability (K := K) M c₁ c₂ ℓ start tie (fun ω =>
      ∀ (k : Fin K) (h : Fin H),
        let x := (ω k).2 h.castSucc
        let a := episodeAction (ω k) h
        let ys := (snapshot M c₁ c₂ ℓ ω k.val).observations h x a
        0 < ys.length →
        empiricalVariance ys ≤ variance M h x a (policyValue M (ω k).1 (h.val + 1)) +
          2 * (H : ℝ) * (deltaC6 M c₁ c₂ ℓ ω k h + xiC6 M c₁ c₂ ℓ ω k h) +
          c * varianceRadius S A H ℓ ys.length) := by sorry

end JinQLearning.Bernstein
