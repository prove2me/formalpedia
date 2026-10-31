-- Prove2me | Theorems.Thm_FoundationsRL_TabularRL_lemma17_bellman_residual
-- name    : FoundationsRL.TabularRL.lemma17_bellman_residual
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:21:41.572674+00:00
-- url     : https://prove2.me/theorems/5ce77d70-6fe2-488a-b299-290c1e068407
-- title:
--   Lemma 17 — the Bellman residual of $\bar Q$ is at most $(b_{h,\delta}+b'_{h,\delta})\wedge 1$
-- statement:
--   Let $M$ be a finite-horizon episodic MDP with finite state and action spaces, horizon $H$ and known rewards $r_h(s,a)\in[0,1]$. Let $\widehat P_h(\cdot\mid s,a)$ be probability distributions on the state space, $b_{h,\delta}$ bonus functions, and let $\bar Q_h$ be the value functions of (5.29), assumed to take values in $[0,1]$ as (5.29) declares. Suppose $b'_{h,\delta}:\mathcal S\times\mathcal A\to\mathbb R$ satisfies, for all $h\in[H]$, $s$, $a$,
--
--   $$
--   \max_{V\in\{0,1\}^{\mathcal S}}\Big|\sum_{s'}\widehat P_h(s'\mid s,a)V(s')-\sum_{s'}P^M_h(s'\mid s,a)V(s')\Big|\le b'_{h,\delta}(s,a).
--   $$
--
--   Then for every $h\in[H]$ the Bellman residual against the true Bellman operator $\mathcal T^M_h$ satisfies, pointwise,
--
--   $$
--   \bar Q_h-\mathcal T^M_h\bar Q_{h+1}\le\big(b_{h,\delta}+b'_{h,\delta}\big)\wedge1 .
--   $$
--
--   Combined with Lemma 15, this bounds the per-episode regret of the greedy policy by the bonuses collected along its own trajectory.
--
--   **Formalization Note** Layers are $0$-indexed; $\mathcal T^M_h Q(s,a)=r_h(s,a)+\mathbb E_{s'\sim P^M_h(\cdot\mid s,a)}\max_{a'}Q(s',a')$ is the published `bellmanOp`.
--
--   Differences from the source:
--
--   - generalization: Assumption 6 also assumes $V^{M,\star}_1(s)\in[0,1]$ → no assumption on the optimal values; reason: the lemma does not involve $V^{M,\star}$; the source's statement is the special case with that assumption added
--   - reading: (5.29) declares $\bar Q_h:\mathcal S\times\mathcal A\to[0,1]$ → hypothesis $\bar Q_h(s,a)\ge0$ for all $h<H$, $s$, $a$ (the bound $\le1$ holds by the clipping); reason: the declared range is used in the proof ("$\le1$ is immediate" and the maximization over $[0,1]^S$ in (5.36)); stated as a hypothesis rather than through a sign condition on $b$, which is weaker
--   - encoding: layers $h=1,\dots,H$, $\bar Q_{H+1}\equiv0$, $x\wedge1$ → layers $0,\dots,H-1$, `optQ` $=0$ from layer $H$ on, `min x 1`; reason: Lean convention of the published `FoundationsRL_RLBasics_Core`; same instances
--   - encoding: estimates $\widehat P_h(\cdot\mid s,a)$ used as distributions → nonnegative vectors summing to 1 at every layer $h<H$; reason: the expectation in (5.28) presupposes a probability distribution; same instances
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Lemma 17, Eqs. (5.32)–(5.33), pp. 91–92; Assumption 6, p. 89; Eq. (5.29), p. 90

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core
import Definitions.Def_FoundationsRL_TabularRL_optQ

namespace FoundationsRL.TabularRL

open FoundationsRL.RLBasics

/-- **Lemma 17** (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive
Decision Making*, arXiv:2312.16730v1, Lemma 17, Eqs. (5.32)–(5.33), pp. 91–92): if `b'_{h,δ}(s,a)`
dominates the error of the estimated transitions `P̂_h(·∣s,a)` uniformly over all `0/1`-valued
functions on `S`, then the Bellman residual of the value functions `Q̄_h` of (5.29) against the
true Bellman operator `T^M_h` (5.10) satisfies
`Q̄_h − T^M_h Q̄_{h+1} ≤ (b_{h,δ} + b'_{h,δ}) ∧ 1` pointwise, for every layer `h ∈ [H]`.

Standing assumptions of §5.6 (Assumption 6, p. 89): known rewards `r_h = R^M_h` with values in
`[0,1]`; the functions of (5.29) take values in `[0,1]` (`Q̄_h : S × A → [0,1]`, p. 90).

**Formalization Note.** Layers are `0`-indexed (`h < H` is the book's `h + 1 ∈ [H]`); `∧ 1` is
`min · 1`; `bellmanOp M h Q` is `T^M_h Q` with `Q = Q̄_{h+1}`. The upper end of the range
`[0,1]` holds by the clipping in (5.29); the lower end is the hypothesis `hQ`, exactly the
book's declaration of the range. The value normalization `V^{M,⋆}_1 ∈ [0,1]` of Assumption 6 is
not needed and not assumed. `P̂_h(·∣s,a)` is a probability vector on `S`. -/
theorem lemma17_bellman_residual {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    [DecidableEq S] [DecidableEq A] {H : ℕ} (M : EpisodicMDP S A H)
    (hR : ∀ h, h < H → ∀ s a, 0 ≤ M.R h s a ∧ M.R h s a ≤ 1)
    (Phat : ℕ → S → A → S → ℝ) (hPhat_nonneg : ∀ h, h < H → ∀ s a s', 0 ≤ Phat h s a s')
    (hPhat_sum : ∀ h, h < H → ∀ s a, ∑ s' : S, Phat h s a s' = 1)
    (b b' : ℕ → S → A → ℝ)
    (hQ : ∀ h, h < H → ∀ s a, 0 ≤ optQ H M.R Phat b h s a)
    (hb' : ∀ h, h < H → ∀ s a, ∀ W : S → ℝ, (∀ s', W s' = 0 ∨ W s' = 1) →
      |∑ s' : S, Phat h s a s' * W s' - ∑ s' : S, M.P h s a s' * W s'| ≤ b' h s a) :
    ∀ h, h < H → ∀ s a,
      optQ H M.R Phat b h s a - bellmanOp M h (optQ H M.R Phat b (h + 1)) s a
        ≤ min (b h s a + b' h s a) 1 := by sorry

end FoundationsRL.TabularRL
