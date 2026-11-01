-- Prove2me | Theorems.Thm_OfflineRLFastRates_optimality_greedy
-- name    : OfflineRLFastRates.optimality_greedy
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:27:24.281458+00:00
-- url     : https://prove2.me/theorems/1a4425db-d290-49c3-ac40-4340829c0124
-- title:
--   p.3 — $V^*=V^{\pi^*}$, $V^*(s)=V^{\pi^*}(s)$ and $Q^*=Q^{\pi^*}$ for a $Q^*$-greedy $\pi^*$
-- statement:
--   Consider a discounted MDP on a measurable state space $\mathcal S$ with a finite nonempty action set $\mathcal A$, Markov transition and reward kernels, a bounded mean reward and $0<\gamma<1$, with initial distribution $\mu$. Let $V^*=\sup_\pi V^\pi$, $V^*(s)=\sup_\pi V^\pi(s)$ and $Q^*(s,a)=\sup_\pi Q^\pi(s,a)$, the suprema over Markov policies. If $\pi^*$ is a measurable deterministic policy with $\pi^*(s)\in\arg\max_{a\in\mathcal A}Q^*(s,a)$ for every $s$, then
--   $$V^*=V^{\pi^*},\qquad V^*(s)=V^{\pi^*}(s)\ \text{ for all } s,\qquad Q^*(s,a)=Q^{\pi^*}(s,a)\ \text{ for all } (s,a).$$
--
--   Acting greedily with respect to the optimal $Q$-function is optimal; this is what makes the regret of a greedy policy comparable with the $Q^*$-gaps of its actions.
--
--   **Formalization Note** $\pi^*$ enters through its Dirac kernel, which requires $\pi^*$ to be measurable.
--
--   Differences from the source:
--   - encoding: a deterministic policy $\pi^*$ → a measurable map; reason: on a measurable state space a deterministic policy must be measurable for its trajectory distribution to exist.
--   - encoding: the mean reward $r(s,a)$ → bounded; reason: the paper uses this item only under Theorem 1's hypothesis $\|Q^*\|_\infty\le Q_{\max}$, which forces a bounded $r$; for unbounded $r$ the series and the $\max_\pi$ of p.3 can be undefined or unattained, and Lean's suprema, series and integrals would return junk values.
--   - encoding: policies $\pi(a\mid s)$, $\max_\pi$ and a finite action space → Markov kernels, suprema over them, and a finite nonempty type with measurable singletons; reason: Lean convention for the source's stationary stochastic policies; the maxima are attained, so the suprema are the same numbers, an MDP has at least one action, and a finite action space carries the discrete $\sigma$-algebra.
-- source:
--   Hu, Kallus, Uehara, Fast Rates for the Regret of Offline Reinforcement Learning, arXiv:2102.00479v2, §1.1, p.3 ("Notice that V* = V^{π*}, V*(s) = V^{π*}(s), Q*(s, a) = Q^{π*}(s, a)")

import Mathlib
import Definitions.Def_OffPolicyDRL_CrossFit_MDP
import Definitions.Def_OfflineRLFastRates_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OfflineRLFastRates

open OffPolicyDRL.CrossFit

/-- Optimality of a `Q*`-greedy policy (Hu, Kallus, Uehara, Fast Rates for the Regret of Offline
Reinforcement Learning, arXiv:2102.00479v2, §1.1, p.3: "Notice that `V* = V^{π*}`,
`V*(s) = V^{π*}(s)`, `Q*(s, a) = Q^{π*}(s, a)`").

For every measurable deterministic `π*` with `π*(s) ∈ argmax_a Q*(s, a)` for all `s`:
`V* = V^{π*}`, `V*(s) = V^{π*}(s)` for every `s`, and `Q*(s, a) = Q^{π*}(s, a)` for every `(s, a)`.

**Formalization Note** `V*`, `V*(s)`, `Q*` are suprema over Markov policies; `π*` enters as its
Dirac kernel, which needs `π*` measurable. The mean reward is assumed bounded. -/
theorem optimality_greedy {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    [Fintype A] [Nonempty A] [MeasurableSingletonClass A]
    (M : MDP S A) [IsMarkovKernel M.P] [IsMarkovKernel M.Rw]
    (hr : ∃ R : ℝ, ∀ x, |M.meanReward x| ≤ R)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (μ : Measure S) [IsProbabilityMeasure μ]
    (πs : S → A) (hπs : Measurable πs) (hgreedy : IsGreedy (QStar M γ) πs) :
    VStar M γ μ = policyValue M γ μ (Kernel.deterministic πs hπs) ∧
    (∀ s, VStarFun M γ s = M.vFun γ (Kernel.deterministic πs hπs) s) ∧
    (∀ x, QStar M γ x = M.qFun γ (Kernel.deterministic πs hπs) x) := by sorry

end OfflineRLFastRates
