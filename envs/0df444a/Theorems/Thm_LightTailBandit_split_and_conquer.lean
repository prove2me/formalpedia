-- Prove2me | Theorems.Thm_LightTailBandit_split_and_conquer
-- name    : LightTailBandit.split_and_conquer
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:25:53.402436+00:00
-- url     : https://prove2.me/theorems/f4a7db0d-6e3c-4fb0-90dd-650fe42cecc2
-- title:
--   Proof of Theorem 5, App. pp.19–20 — split-and-conquer: a large pseudo regret forces a large $(n_k-1)\Delta_k$ in $\mathcal A_0$ or a large $\Delta_k$ outside
-- statement:
--   Throughout, $K\ge2$ arms and a horizon $T$ with $T\ge3$ and $T\ge K$ are fixed, $\sigma>0$, rounds are $t=1,\dots,T$, and the reward of round $t$ is $r_{t,a_t}=\theta_{a_t}+\epsilon_{t,a_t}$, where the noise $\epsilon_{t,k}$ of round $t$ and arm $k$ is independent of everything observed before round $t$ and is $\sigma$-sub-Gaussian: $\mathbb E[e^{\lambda\epsilon_{t,k}}]\le e^{\lambda^2\sigma^2/2}$ for all real $\lambda$. The action $a_t$ may depend only on the past (and on independent internal randomization). $n_k$ is the number of pulls of arm $k$ in the $T$ rounds, $\theta_*=\max_k\theta_k$, $\Delta_k=\theta_*-\theta_k\le1$, and the bonus is $\mathrm{rad}(n)=\sigma\sqrt{\ln T/n}\,\max\{\sqrt{\eta_1T/(nK)},\sqrt{\eta_2}\}$ (6).
--
--   Let $b$ be an optimal arm and $x\ge2K$. For every sequence of actions, if
--   $$
--   R(T)\ge x\left(1-\frac{1}{2\sqrt K}\right),
--   $$
--   then some arm $k\ne b$ satisfies either
--   $$
--   (n_k-1)\Delta_k\ge\frac{x-2K}{4K}\ \text{ and }\ k\in\mathcal A_0,\qquad\text{or}\qquad \Delta_k\ge\frac{x-2K}{4T}\ \text{ and }\ k\notin\mathcal A_0 .
--   $$
--
--   A union bound over the arms turns this into the decomposition of $P(R(T)\ge x(1-1/(2\sqrt K)))$ into the four terms bounded by (19), (21), (22), (24) for SE and the two terms bounded by (25), (26) for UCB. Splitting along the random set $\mathcal A_0$ is what brings the factor $K$ down to $\sqrt K$.
--
--   **Formalization Note** $n_k-1$ is real subtraction ($-\Delta_k$ when $n_k=0$, as in the page's sum).
--
--   Differences from the source:
--   - encoding: a chain of probability inequalities P(R ≥ x(1−1/(2√K))) ≤ Σ_{k≠1}(P(…, k ∈ A₀) + P(…, k ∉ A₀)), justified by showing that the opposite inequalities 'cannot hold' simultaneously → the pathwise inclusion: R ≥ x(1 − 1/(2√K)) implies some k ≠ b is in one of the two events; reason: the union bound over this inclusion is each printed step; the page's own justification is this pathwise claim
--   - reading: x(1 − 1/√K) in the line 'Therefore, P(R ≥ x(1 − 1/√K))' (p.20) and in part (b) (p.23) → x(1 − 1/(2√K)); reason: the argument starts from x(1 − 1/(2√K)) on p.19 and only that form is proved: the closing step x(1 − 1/(2√K)) − K ≥ (x − 2K)/2 fails with 1/√K for K < 4
--   - generalization: for the actions of SE or UCB → for every sequence of actions; reason: the inclusion uses only Σ_k n_k = T and Δ_k ≤ 1; it specializes to both policies
--   - generalization: arm 1 is the optimal arm (WLOG), k ≠ 1 → b is any arm with θ b = θ_*, k ≠ b; reason: with several optimal arms every choice of b is covered; it specializes to the paper's arm 1
--   - encoding: Let x ≥ 2K (part 2 of the proof) → 2K ≤ x as a hypothesis; reason: as printed
--   - encoding: rounds t = 1, …, T and arms [K] → rounds 0, …, T − 1 (Lean round t is the paper's round t + 1) and Fin K; reason: Lean convention; same instances
-- source:
--   Simchi-Levi, Zheng, Zhu, A Simple and Optimal Policy Design with Safety against Heavy-Tailed Risk for Stochastic Bandits, arXiv:2206.02969v6, Online Appendix, proof of Theorem 5, part 2, pp.19–20 (PDF pp.56–57)

import Mathlib
import Definitions.Def_FoundationsRL_Bandits_pullCount
import Definitions.Def_LightTailBandit_IsNoiseModel
import Definitions.Def_LightTailBandit_reward
import Definitions.Def_LightTailBandit_pseudoRegret
import Definitions.Def_LightTailBandit_rad
import Definitions.Def_LightTailBandit_IsUCBRun
import Definitions.Def_LightTailBandit_IsSERun
import Definitions.Def_LightTailBandit_goodEvent

open MeasureTheory ProbabilityTheory FoundationsRL.Bandits

namespace LightTailBandit

/-- **Split-and-conquer decomposition** (Simchi-Levi, Zheng, Zhu, *A Simple and Optimal Policy Design with Safety against Heavy-Tailed Risk
for Stochastic Bandits*, arXiv:2206.02969v6, Online Appendix, proof of
Theorem 5, part 2, pp.19–20 (PDF pp.56–57)).

For any sequence of actions, gaps at most `1`, an optimal arm `b` and `x ≥ 2K`: if the pseudo
regret is at least `x(1 − 1/(2√K))`, then some arm `k ≠ b` has either
`(n_k − 1)Δ_k ≥ (x − 2K)/(4K)` and `k ∈ A₀`, or `Δ_k ≥ (x − 2K)/(4T)` and `k ∉ A₀`.

**Formalization Note.** Rounds are 0-based and `n_k = pullCount h T k`; `n_k − 1` is real
subtraction. The page's chain of probability bounds is the union bound over this pathwise
inclusion. The factor is `1 − 1/(2√K)` as at the start of the argument (p.19); the page's later
"`1 − 1/√K`" is a misprint. -/
theorem split_and_conquer {K T : ℕ} (hK : 2 ≤ K) (hT : 3 ≤ T) (hKT : K ≤ T)
    (θ : Fin K → ℝ) (hgap : ∀ k, gap θ k ≤ 1)
    (h : ℕ → Fin K) (b : Fin K) (hb : θ b = θstar θ) (x : ℝ) (hx : 2 * K ≤ x)
    (hR : x * (1 - 1 / (2 * Real.sqrt K)) ≤ pseudoRegret θ T h) :
    ∃ k, k ≠ b ∧
      (((x - 2 * K) / (4 * K) ≤ ((pullCount h T k : ℝ) - 1) * gap θ k ∧ inA0 T h b k) ∨
        ((x - 2 * K) / (4 * T) ≤ gap θ k ∧ ¬ inA0 T h b k)) := by sorry

end LightTailBandit
