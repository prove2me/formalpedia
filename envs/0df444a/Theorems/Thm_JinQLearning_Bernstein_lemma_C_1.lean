-- Prove2me | Theorems.Thm_JinQLearning_Bernstein_lemma_C_1
-- name    : JinQLearning.Bernstein.lemma_C_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:37:27.111694+00:00
-- url     : https://prove2.me/theorems/4cfa5074-aec8-46eb-ac6d-f584b0b5226b
-- title:
--   Lemma C.1 — recursion on Q
-- statement:
--   For every positive S,A,H,K, bounded-reward stage-dependent MDP, positive c1,c2 and p in (0,1), replay any sequence of episode policies and states using (C.1)-(C.3). For each episode k, stage h and pair (x,a), let t be the number of earlier visits and k_i their episode indices. Then
--   $$ (Q_h^k-Q_h^\star)(x,a)=\alpha_t^0(H-Q_h^\star(x,a))+\sum_{i=1}^t\alpha_t^i[(V_{h+1}^{k_i}-V_{h+1}^\star)(x_{h+1}^{k_i})+[(\widehat P_h^{k_i}-P_h)V_{h+1}^\star](x,a)+b_i(x,a,h)]. $$
--   The identity includes t=0. It also holds for replayed action/outcome paths without greedy or positive-probability assumptions.
--
--   Differences from the source:
--   - encoding: finite nonempty state/action sets and one-based stages and episodes → Fin S, Fin A, Fin H, Fin K with NeZero instances and zero-based indices; reason: finite relabeling preserves every positive cardinality, horizon and episode count; index h represents source stage h+1
--   - encoding: stage-dependent transitions and rewards in [0,1] → the published nonstationary MDP with a common action set via equivalences, reward equal to negative cost, and the [0,1] reward bounds; reason: cost/reward sign conversion and action relabeling are exact; arbitrary real transition rows remain independent across stages, and unused stages beyond H are unrestricted
--   - encoding: conditional expected policy values and optimal values → finite backward recursions with terminal zero and nonempty finite maxima; reason: these construct the Bellman values on precisely the finite-horizon model without assuming value equations
--   - encoding: N, mu, sigma and previous beta stored for each triple → chronological lists of observed next-stage values, with N=length, mu=sum, sigma=sum of squares and beta computed from the list; reason: the same historical values give exactly the stated accumulators and updates; no claim about the storage complexity of the encoding is made
--   - reading: Theorem 2 invokes (C.3) but Algorithm 2 line 10 has (sigma-mu^2)/t → use the explicit (C.1)-(C.3) centered variance sigma/t-(mu/t)^2 and beta_0=0; reason: the theorem explicitly specifies these equations; the contradictory pseudocode is recorded in insight I1
--   - encoding: visits k_1,...,k_t with weights alpha_t^i → a masked sum over previous episode indices j with visit rank N_h^j(x,a)+1; reason: each earlier visit occurs once and the chronological rank is exactly i
--   - generalization: the identity on the generated Q-learning run → the same identity on every replayed policy/outcome path; reason: the deterministic update identity does not require greediness or positive transition mass; every generated run is included
-- source:
--   Jin, Allen-Zhu, Bubeck & Jordan, Is Q-learning Provably Efficient?, arXiv:1807.03765v1, p. 15, Lemma C.1.

import Definitions.Def_JinQLearning_Bernstein_Statistics

open scoped BigOperators

namespace JinQLearning.Bernstein

theorem lemma_C_1 {S A H K : ℕ} [NeZero S] [NeZero A] [NeZero H] [NeZero K]
    (M : Model S A H) (c₁ c₂ p : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hp : 0 < p) (hp' : p < 1) (ω : Path S A H K)
    (k : Fin K) (h : Fin H) (x : Fin S) (a : Fin A) :
    let ℓ := iota S A H K p
    let q := snapshot M c₁ c₂ ℓ ω k.val
    q.Q h x a - optimalQ M h x a =
      VLearning.CCE.lrW H (q.observations h x a).length 0 * ((H : ℝ) - optimalQ M h x a) +
      visitSum M c₁ c₂ ℓ ω k h x a (fun j =>
        nextError M c₁ c₂ ℓ ω j h +
        (optimalValue M (h.val + 1) ((ω j).2 h.succ) -
          expectation M h x a (optimalValue M (h.val + 1))) +
        visitBonus (snapshot M c₁ c₂ ℓ ω j.val) c₁ c₂ ℓ h x a ((ω j).2 h.succ)) := by sorry

end JinQLearning.Bernstein
