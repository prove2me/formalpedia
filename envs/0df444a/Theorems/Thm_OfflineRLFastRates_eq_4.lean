-- Prove2me | Theorems.Thm_OfflineRLFastRates_eq_4
-- name    : OfflineRLFastRates.eq_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:27:23.69147+00:00
-- url     : https://prove2.me/theorems/01888cd7-39e0-4f02-90b4-52d8c8b122f1
-- title:
--   Eq. (4) — performance difference: $(1-\gamma)(V^*-V^{\pi})=\mathbb E_{s\sim d^{\pi}}[Q^*(s,\pi^*(s))-Q^*(s,\pi(s))]$
-- statement:
--   Consider a discounted MDP on a measurable state space $\mathcal S$ with a finite nonempty action set $\mathcal A$, Markov transition and reward kernels, a bounded mean reward, $0<\gamma<1$ and an initial distribution $\mu$. Let $\pi^*$ be a measurable deterministic policy with $\pi^*(s)\in\arg\max_aQ^*(s,a)$, and let $A^*(s,a)=Q^{\pi^*}(s,a)-V^{\pi^*}(s)$. Then $A^*(s,a)\le0$ for all $(s,a)$, and for every measurable deterministic policy $\pi$, with $d^\pi$ its average state occupancy distribution,
--   $$(1-\gamma)\big(V^*-V^{\pi}\big)=\mathbb E_{s\sim d^{\pi}}\big[-A^*(s,\pi(s))\big]=\mathbb E_{s\sim d^{\pi}}\big[Q^*(s,\pi^*(s))-Q^*(s,\pi(s))\big].$$
--
--   This is the performance difference lemma in the form used to start the proof of Theorem 1: it turns the regret of $\pi$ into the occupancy-average of the $Q^*$-gap of the actions $\pi$ chooses.
--
--   **Formalization Note** $d^\pi$ is the measure $(1-\gamma)\sum_t\gamma^t\,\mathbb P^\pi(s_t\in\cdot)$ with $s_0\sim\mu$, and the expectations are integrals of bounded measurable functions against it.
--
--   Differences from the source:
--   - generalization: the data-driven policy $\hat\pi$ for a fixed dataset → every measurable deterministic policy $\pi$; reason: the identity uses nothing about $\hat\pi$, and $\pi=\hat\pi$ for each dataset is the source's instance.
--   - encoding: deterministic policies $\pi^*$, $\hat\pi$ → measurable maps; reason: on a measurable state space a deterministic policy must be measurable for its trajectory distribution to exist.
--   - encoding: the mean reward $r(s,a)$ → bounded; reason: the paper uses this item only under Theorem 1's hypothesis $\|Q^*\|_\infty\le Q_{\max}$, which forces a bounded $r$; for unbounded $r$ the series and the $\max_\pi$ of p.3 can be undefined or unattained, and Lean's suprema, series and integrals would return junk values.
--   - encoding: policies $\pi(a\mid s)$, $\max_\pi$ and a finite action space → Markov kernels, suprema over them, and a finite nonempty type with measurable singletons; reason: Lean convention for the source's stationary stochastic policies; the maxima are attained, so the suprema are the same numbers, an MDP has at least one action, and a finite action space carries the discrete $\sigma$-algebra.
-- source:
--   Hu, Kallus, Uehara, Fast Rates for the Regret of Offline Reinforcement Learning, arXiv:2102.00479v2, §7.1, p.16, Eq. (4)

import Mathlib
import Definitions.Def_OffPolicyDRL_CrossFit_MDP
import Definitions.Def_OfflineRLFastRates_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OfflineRLFastRates

open OffPolicyDRL.CrossFit

/-- Eq. (4), performance difference (Hu, Kallus, Uehara, Fast Rates for the Regret of Offline
Reinforcement Learning, arXiv:2102.00479v2, §7.1, p.16).

Let `A*(s, a) = Q^{π*}(s, a) − V^{π*}(s)` for a measurable `Q*`-greedy `π*`. Then `A* ≤ 0`, and for
every measurable deterministic policy `π`
`(1 − γ)(V* − V^π) = E_{s∼d^π}[−A*(s, π(s))] = E_{s∼d^π}[Q*(s, π*(s)) − Q*(s, π(s))]`.

**Formalization Note** The paper applies the identity to `π = π̂` for a fixed dataset; it is stated
here for every measurable deterministic `π`. `d^π` is `M.discVisitation γ µ π` and the
expectations are Bochner integrals of bounded measurable functions against it. -/
theorem eq_4 {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    [Fintype A] [Nonempty A] [MeasurableSingletonClass A]
    (M : MDP S A) [IsMarkovKernel M.P] [IsMarkovKernel M.Rw]
    (hr : ∃ R : ℝ, ∀ x, |M.meanReward x| ≤ R)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (μ : Measure S) [IsProbabilityMeasure μ]
    (πs : S → A) (hπs : Measurable πs) (hgreedy : IsGreedy (QStar M γ) πs)
    (π : S → A) (hπ : Measurable π) :
    (∀ s a, M.qFun γ (Kernel.deterministic πs hπs) (s, a)
        - M.vFun γ (Kernel.deterministic πs hπs) s ≤ 0) ∧
    (1 - γ) * (VStar M γ μ - policyValue M γ μ (Kernel.deterministic π hπ)) =
      ∫ s, -(M.qFun γ (Kernel.deterministic πs hπs) (s, π s)
        - M.vFun γ (Kernel.deterministic πs hπs) s)
        ∂(M.discVisitation γ μ (Kernel.deterministic π hπ)) ∧
    (1 - γ) * (VStar M γ μ - policyValue M γ μ (Kernel.deterministic π hπ)) =
      ∫ s, (QStar M γ (s, πs s) - QStar M γ (s, π s))
        ∂(M.discVisitation γ μ (Kernel.deterministic π hπ)) := by sorry

end OfflineRLFastRates
