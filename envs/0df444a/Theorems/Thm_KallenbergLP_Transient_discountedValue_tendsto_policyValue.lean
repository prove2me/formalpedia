-- Prove2me | Theorems.Thm_KallenbergLP_Transient_discountedValue_tendsto_policyValue
-- name    : KallenbergLP.Transient.discountedValue_tendsto_policyValue
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:40:38.915987+00:00
-- url     : https://prove2.me/theorems/6bfaa0d1-9af4-49fd-8f25-561987c0e4ab
-- title:
--   Lemma 3.2.1 — the discounted reward tends to the total reward as the discount factor tends to 1
-- statement:
--   Consider a finite Markov decision model with substochastic transitions and real rewards $r_{ia}$, and assume (Assumption 3.2.1) that for every initial state and every policy the expected total reward $v_i(R)=\lim_{T\to\infty}\sum_{t=1}^Tv_i^t(R)$ exists in $[-\infty,+\infty]$. For $\delta\in[0,1)$ let $v_i^\delta(R)=\sum_{t=1}^\infty\delta^{t-1}v_i^t(R)$ be the expected discounted reward.
--
--   Then for any initial state $i$ and any policy $R$,
--
--   $$\lim_{\delta\uparrow1}v_i^\delta(R)=v_i(R),$$
--
--   with the limit taken in $[-\infty,+\infty]$; in particular $v_i^\delta(R)\to+\infty$ when $v_i(R)=+\infty$ and $v_i^\delta(R)\to-\infty$ when $v_i(R)=-\infty$.
--
--   This Abelian limit is what transfers Blackwell optimality of a pure stationary policy to total optimality in Theorem 3.2.1.
--
--   **Formalization Note** The limit $\delta\uparrow1$ is the filter of left neighbourhoods of $1$, and the real discounted value is coerced to `EReal`. The total reward is the `limsup` of the partial sums, which is the limit under the assumption.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 37, Assumption 3.2.1 and Lemma 3.2.1

import Definitions.Def_KallenbergLP_Transient_TotalReward
set_option autoImplicit false

namespace KallenbergLP.Transient

/-- Lemma 3.2.1: under Assumption 3.2.1, `lim_{δ ↑ 1} v^δ_i(R) = v_i(R)` in `[-∞, +∞]`. -/
theorem discountedValue_tendsto_policyValue
    {N : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (M : MDP N α) (r : Fin N → α → ℝ)
    (hreward : TotalRewardExists M r) (i : Fin N) (R : Policy M) :
    Filter.Tendsto (fun δ : ℝ => (discountedValue M r R i δ : EReal))
      (nhdsWithin 1 (Set.Iio 1)) (nhds (policyValue M r R i)) := by sorry

end KallenbergLP.Transient
