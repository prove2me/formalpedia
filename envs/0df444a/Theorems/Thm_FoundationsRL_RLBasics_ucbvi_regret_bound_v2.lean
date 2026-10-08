-- Prove2me | Theorems.Thm_FoundationsRL_RLBasics_ucbvi_regret_bound_v2
-- name    : FoundationsRL.RLBasics.ucbvi_regret_bound_v2
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:19:42.987991+00:00
-- url     : https://prove2.me/theorems/3b1307b7-4a0e-4cc4-b321-ca07642a20d4
-- title:
--   Theorem 1 — UCB-VI regret bound (v2: optimistic bonus for unvisited pairs)
-- statement:
--   This is **Theorem 1** of Foster & Rakhlin (arXiv:2312.16730v1, p. 90), the chapter's headline regret bound for tabular online reinforcement learning.
--
--   Fix a finite-horizon episodic MDP $M$ with finite state space $\mathcal S$ ($|\mathcal S|=S$), finite action space $\mathcal A$ ($|\mathcal A|=A$) and horizon $H$, satisfying Assumption 6: the reward at each layer is deterministic and known to the learner, given by $r_h:\mathcal S\times\mathcal A\to[0,1]$ (so $M$'s mean reward is $r_h$), and $V^{M,\star}_1(s)\in[0,1]$ for every $s$. The learner interacts with $M$ for $T$ episodes using UCB-VI (§5.6): before episode $t$ it forms the empirical counts $n^t_h(s,a)$, $n^t_h(s,a,s')$ and the estimated transitions $\hat P^t_h$ of Eq. (5.25), computes by backward induction, with $Q^t_{H+1}\equiv 0$,
--   $$Q^t_h(s,a)=\Big\{r_h(s,a)+\mathbb E_{s'\sim\hat P^t_h(\cdot\mid s,a)}\big[\max_{a'}Q^t_{h+1}(s',a')\big]+b^t_{h,\delta}(s,a)\Big\}\wedge 1,\qquad b^t_{h,\delta}(s,a)=2\sqrt{\frac{\log(2SAHT/\delta)}{n^t_h(s,a)}}$$
--   (Eqs. (5.26)–(5.27); for an unvisited pair $n^t_h(s,a)=0$ the bonus is $+\infty$ and the clipped value is $1$), and plays the policy greedy with respect to $Q^t$.
--
--   **Theorem.** There is a universal constant $C>0$ such that for every such instance, every $T$ and every $\delta>0$, with probability at least $1-\delta$ over the $T$ episodes,
--   $$\mathrm{Reg}=\sum_{t=1}^T\big(f^M(\pi_M)-f^M(\pi^t)\big)\le C\cdot H\,S\,\sqrt{A\,T}\,\sqrt{\log(SAHT/\delta)} .$$
--
--   **Formalization Note.** The retired version used a definition module in which the bonus formula was evaluated at $n^t_h(s,a)=0$ through Lean's $x/0=0$, so an unvisited pair received bonus $0$ and the non-optimistic value $r_h(s,a)\wedge 1$; the resulting learner is not UCB-VI and can fail to explore (the accepted disproof). The new statement imports `FoundationsRL_RLBasics_UCBVI_v2`, whose `ucbQ` gives every unvisited pair the book's clipped value $1$; all other definitions are unchanged. Conventions made explicit: the $T$-episode interaction is a finite probability space (sums over the finite type of $T$-episode outcomes); rewards are deterministic and equal to $r_h$ (Assumption 6); the terminal convention is $Q^t_{H+1}\equiv 0$ as in the book's analysis (Eq. (5.29), Lemma 16) — the algorithm box's "$\bar V^t_{H+1}\equiv 1$" is treated as a misprint; the greedy policy breaks ties by the first maximizer; the universal constant hidden in the book's $\lesssim$ is quantified before every instance; the retired hypothesis $\delta\le 1$ is dropped since the book states the result for any $\delta>0$ (for $\delta>1$ it is trivial). For $T=0$ or $H=0$ both sides are $0$.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, p. 89–90, Theorem 1, Assumption 6, Eqs. (5.25)–(5.27)

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core
import Definitions.Def_FoundationsRL_RLBasics_UCBVI_v2

namespace FoundationsRL.RLBasics

/-- **Theorem 1** (Foster–Rakhlin, arXiv:2312.16730v1, p. 90, Thm. 1): under Assumption 6
(deterministic, known, `[0,1]`-bounded rewards `r` and `V^{M,⋆}_1 ∈ [0,1]`), for any `δ > 0`
and any number of episodes `T`, UCB-VI with the bonus `b^t_{h,δ}(s,a) = 2√(log(2SAHT/δ)/n^t_h(s,a))`
of Eq. (5.27) achieves, with probability at least `1 - δ` over its `T` episodes of interaction
with `M`, regret at most a universal constant times `H·S·√(A·T)·√(log(S·A·H·T/δ))`.

Corrected replacement of `ucbvi_regret_bound`: the retired statement used
`Def_FoundationsRL_RLBasics_UCBVI`, whose `ucbQ` gave an unvisited pair (`n^t_h(s,a) = 0`) the
bonus `0` (Lean's `x / 0 = 0`) instead of the book's `+∞`, so the formalized learner was not
optimistic and could fail to explore. `Def_FoundationsRL_RLBasics_UCBVI_v2` implements the
book's clipped value `Q^t_h(s,a) = 1` for unvisited pairs; nothing else changes, except that
the superfluous hypothesis `δ ≤ 1` is dropped (the book says "for any `δ > 0`"; for `δ > 1`
the claim is trivial). -/
theorem ucbvi_regret_bound_v2 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {S A : Type} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A]
        {H : ℕ} (M : EpisodicMDP S A H) (r : ℕ → S → A → ℝ),
        (∀ h, h < H → ∀ s a, r h s a ∈ Set.Icc (0 : ℝ) 1) →
        (∀ h, h < H → ∀ s a, M.R h s a = r h s a) →
        (∀ s : S, Vstar M 0 s ∈ Set.Icc (0 : ℝ) 1) →
        ∀ (T : ℕ) (δ : ℝ), 0 < δ →
        probEvent M (ucbviLearner M r δ T) T
            (fun histT => regret M r δ T histT ≤
              C * (H : ℝ) * (Fintype.card S : ℝ) * Real.sqrt ((Fintype.card A : ℝ) * T) *
                Real.sqrt (Real.log ((Fintype.card S : ℝ) * (Fintype.card A : ℝ) * H * T / δ)))
          ≥ 1 - δ := by sorry

end FoundationsRL.RLBasics
