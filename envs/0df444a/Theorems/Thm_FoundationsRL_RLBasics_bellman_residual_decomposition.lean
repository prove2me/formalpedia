-- Prove2me | Theorems.Thm_FoundationsRL_RLBasics_bellman_residual_decomposition
-- name    : FoundationsRL.RLBasics.bellman_residual_decomposition
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T05:03:02.3731+00:00
-- url     : https://prove2.me/theorems/8f822035-1064-4f11-9239-2e69a6d7c834
-- title:
--   Lemma 14 — Bellman residual decomposition
-- statement:
--   Where the Performance Difference Lemma compares two policies under one MDP, the Bellman residual decomposition compares one policy's performance under two *different* MDPs.
--
--   Fix two finite-horizon episodic MDPs $M, M'$ sharing the same state space, action space and horizon (but possibly different transitions and rewards), a state $s$, and a policy $\pi \in \Pi^{\mathrm{rns}}$. The lemma states
--
--   $$V^{M,\pi}_1(s) - V^{M',\pi}_1(s) = \sum_{h=1}^{H} \mathbb E^{M',\pi}_{s_h}\Big[\textstyle\sum_a \pi_h(a\mid s_h)\big(Q^{M,\pi}_h(s_h,a) - R'_h(s_h,a) - \textstyle\sum_{s'} P'_h(s'\mid s_h,a)\, V^{M,\pi}_{h+1}(s')\big)\Big],$$
--
--   where the outer expectation rolls $\pi$ into $M'$ (i.e. uses $M'$'s own dynamics to reach the layer-$h$ state), and the bracketed term at each layer is exactly the *Bellman residual* of $M$'s value function $Q^{M,\pi}$ evaluated against $M'$'s reward and transition — how far $M$'s $Q$-function is from being self-consistent under $M'$'s own dynamics. This is the tool used to bound the price of planning in an *estimated* MDP $\widehat M$ in place of the truth: it converts a gap in value under two different models into a sum of per-layer transition/reward estimation errors, each weighted by the true value function.
--
--   **Formalization Note** Layers are $0$-indexed. The lemma is stated for the special case $M' = \widehat M$ shares $M$'s initial state distribution is not required here, since $s$ is supplied directly (matching Eq. (5.18), the per-state form of the lemma, rather than Eq. (5.19), its corollary for $f^M(\pi)-f^{\widehat M}(\pi)$ which additionally assumes a shared $d_1$).
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, p. 86, Lemma 14, Eq. (5.18)

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core

namespace FoundationsRL.RLBasics

/-- **Lemma 14 (Bellman residual decomposition)** (Foster–Rakhlin, arXiv:2312.16730v1, p. 86,
Lemma 14, Eq. (5.18)): for any pair of MDPs `M`, `M'` (same `S`, `A`, `H`) and any
`s ∈ S`, `π ∈ Π^{rns}`, the difference in initial value of the *same* policy `π` under `M`
versus `M'` decomposes, layer by layer, as the `(M', π)`-roll-in expectation of the Bellman
residual of `M`'s `Q^{M,π}` against `M'`'s dynamics. -/
theorem bellman_residual_decomposition {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    [DecidableEq S] [DecidableEq A] {H : ℕ} (M M' : EpisodicMDP S A H) (π : Policy S A H)
    (hπ : IsPolicy H π) (s : S) :
    V M π 0 s - V M' π 0 s =
      ∑ h ∈ Finset.range H,
        stateExp M' π s h (fun sh =>
          ∑ a : A, π h sh a *
            (Q M π h sh a - (M'.R h sh a + ∑ s' : S, M'.P h sh a s' * V M π (h + 1) s'))) := by sorry

end FoundationsRL.RLBasics
