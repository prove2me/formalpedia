-- Prove2me | Theorems.Thm_FoundationsRL_RLBasics_ucbvi_regret_bound
-- name    : FoundationsRL.RLBasics.ucbvi_regret_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-18T05:04:14.690695+00:00
-- url     : https://prove2.me/theorems/f32d2329-cfe5-4581-b2cb-638eabf069e1
-- title:
--   Theorem 1 — UCB-VI regret bound
-- statement:
--   This is Theorem 1, the chapter's headline result and the only result in the book's Chapter 4–5 material labeled a "Theorem" rather than a "Proposition" or "Lemma": a regret bound, polynomial in the number of states, actions and the horizon, for tabular online reinforcement learning.
--
--   Fix a finite-horizon episodic MDP $M$ with finite state space $S$, finite action space $A$, and horizon $H$, satisfying Assumption 6: the reward at each layer is deterministic and known to the learner, given by a function $r_h : S\times A \to [0,1]$, and $V^{M,\star}_1(s) \in [0,1]$ for every $s$. The learner interacts with $M$ for $T$ episodes using the UCB-VI algorithm (§5.6): at each episode $t$, it recomputes, by backward induction over the layers, value estimates $Q^t_h(s,a) = \big\{r_h(s,a) + \mathbb E_{s'\sim\widehat P^t_h(\cdot\mid s,a)}[V^t_{h+1}(s')] + b^t_{h,\delta}(s,a)\big\}\wedge 1$ from the empirical transition estimates and past visitation counts, using the explicit bonus
--
--   $$b^t_{h,\delta}(s,a) = 2\sqrt{\frac{\log(2SAHT/\delta)}{n^t_h(s,a)}}$$
--
--   (Eq. (5.27)), and plays the policy greedy with respect to $Q^t$.
--
--   The theorem asserts: for any confidence level $\delta \in (0,1]$, there is a universal constant $C$ (not depending on $M$, $S$, $A$, $H$, $T$ or $\delta$) such that, with probability at least $1-\delta$ over the randomness of the $T$ episodes of interaction,
--
--   $$\mathrm{Reg} = \sum_{t=1}^T \big(f^{M}(\pi^{M,\star}) - f^{M}(\pi^t)\big) \;\le\; C \cdot H \cdot S \cdot \sqrt{A\,T} \cdot \sqrt{\log(SAHT/\delta)}.$$
--
--   This shows that optimism (via the confidence bonus) combined with dynamic programming achieves regret polynomial in every relevant parameter of the tabular MDP — in sharp contrast to naive exploration strategies like $\varepsilon$-greedy, which the chapter's "combination lock" example shows can incur regret exponential in the horizon $H$.
--
--   **Formalization Note** Since $S$, $A$, $H$ and $T$ are all finite, the $T$-episode interaction is modeled as a genuinely finite probability space (no measure theory): the "probability at least $1-\delta$" event is a finite sum over the finite type of possible $T$-episode outcomes. The universal constant $C$ is existentially quantified rather than given a literal numeral, since (per the book's own "$\lesssim$" notation on this page) its exact value is not pinned down without carrying out the full proof; this is the explicit-constant convention this mission adopts wherever the source states an asymptotic ($\lesssim$/$O(\cdot)$) bound without proving it here. The empirical-transition estimator used inside $Q^t_h$ is defined as $0$ when $n^t_h(s,a)=0$ (no data yet collected), a boundary case the book's Eq. (5.25) does not address explicitly.
--
--   **Moderator's note.** The constant $C$ hidden in the book's $\lesssim$ is quantified *before* $S, A, H, M, r, T, \delta$: a single absolute constant must work for every instance. Quantifying it after the instance would let $C$ grow with the instance and make the bound vacuous.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, p. 89–90, Thm. 1 and Assumption 6, Eqs. (5.25)–(5.27)

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core
import Definitions.Def_FoundationsRL_RLBasics_UCBVI

namespace FoundationsRL.RLBasics

/-- **Theorem 1** (Foster–Rakhlin, arXiv:2312.16730v1, p. 90, Thm. 1): under Assumption 6
(deterministic, known, `[0,1]`-bounded mean rewards `r` and `V^{M,⋆}_1 ∈ [0,1]`), for any
`δ ∈ (0,1]` and any `T`, UCB-VI with bonus `bonus δ · · H T` (Eq. (5.27)) achieves, with
probability at least `1 - δ` over its `T` episodes of interaction with `M`, regret at most a
universal constant times `H·S·√(A·T)·√(log(S·A·H·T/δ))`. -/
theorem ucbvi_regret_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ {S A : Type} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A]
        {H : ℕ} (M : EpisodicMDP S A H) (r : ℕ → S → A → ℝ),
        (∀ h, h < H → ∀ s a, r h s a ∈ Set.Icc (0 : ℝ) 1) →
        (∀ h, h < H → ∀ s a, M.R h s a = r h s a) →
        (∀ s : S, Vstar M 0 s ∈ Set.Icc (0 : ℝ) 1) →
        ∀ (T : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 →
        probEvent M (ucbviLearner M r δ T) T
            (fun histT => regret M r δ T histT ≤
              C * (H : ℝ) * (Fintype.card S : ℝ) * Real.sqrt ((Fintype.card A : ℝ) * T) *
                Real.sqrt (Real.log ((Fintype.card S : ℝ) * (Fintype.card A : ℝ) * H * T / δ)))
          ≥ 1 - δ := by sorry

end FoundationsRL.RLBasics
