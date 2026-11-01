-- Prove2me | Theorems.Thm_OfflineRLFastRates_exists_measurable_greedy
-- name    : OfflineRLFastRates.exists_measurable_greedy
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:27:30.331055+00:00
-- url     : https://prove2.me/theorems/3f07717b-18df-4e13-ab72-199bbda570dc
-- title:
--   p.3 — a measurable $Q^*$-greedy deterministic policy $\pi^*$ exists
-- statement:
--   Consider a discounted MDP on a measurable state space $\mathcal S$ with a finite nonempty action set $\mathcal A$, Markov transition and reward kernels, a bounded mean reward $r$ and $0<\gamma<1$. Let $Q^*(s,a)=\sup_\pi Q^\pi(s,a)$ be the optimal $Q$-function. Then there is a measurable deterministic policy $\pi^*:\mathcal S\to\mathcal A$ with
--   $$\pi^*(s)\in\arg\max_{a\in\mathcal A}Q^*(s,a)\qquad\text{for every } s\in\mathcal S .$$
--
--   The paper fixes "any deterministic policy with $\pi^*(s)\in\arg\max_a Q^*(s,a)$" throughout; this statement records that such a policy exists as a genuine (measurable) policy, which every later statement about $\pi^*$ presupposes.
--
--   **Formalization Note** Policies are Markov kernels and $Q^*$ is a supremum over them. Measurability is what makes $\pi^*$ a policy (a Dirac kernel).
--
--   Differences from the source:
--   - reading: "We always let $\pi^*$ be any deterministic policy with $\pi^*(s)\in\arg\max_a Q^*(s,a)$" → existence of a measurable such $\pi^*$; reason: the sentence presupposes that such a policy exists, and a deterministic policy on a measurable state space is a measurable map.
--   - encoding: the mean reward $r(s,a)$ → bounded; reason: the paper uses this item only under Theorem 1's hypothesis $\|Q^*\|_\infty\le Q_{\max}$, which forces a bounded $r$; for unbounded $r$ the series and the $\max_\pi$ of p.3 can be undefined or unattained, and Lean's suprema, series and integrals would return junk values.
--   - encoding: policies $\pi(a\mid s)$, $\max_\pi$ and a finite action space → Markov kernels, suprema over them, and a finite nonempty type with measurable singletons; reason: Lean convention for the source's stationary stochastic policies; the maxima are attained, so the suprema are the same numbers, an MDP has at least one action, and a finite action space carries the discrete $\sigma$-algebra.
-- source:
--   Hu, Kallus, Uehara, Fast Rates for the Regret of Offline Reinforcement Learning, arXiv:2102.00479v2, §1.1, p.3 (definition of π*)

import Mathlib
import Definitions.Def_OffPolicyDRL_CrossFit_MDP
import Definitions.Def_OfflineRLFastRates_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OfflineRLFastRates

open OffPolicyDRL.CrossFit

/-- A measurable optimal greedy policy exists (Hu, Kallus, Uehara, Fast Rates for the Regret of
Offline Reinforcement Learning, arXiv:2102.00479v2, §1.1, p.3: "We always let `π*` be any
deterministic policy with `π*(s) ∈ argmax_{a ∈ A} Q*(s, a)`").

In a discounted MDP on a measurable state space with finitely many actions, Markov transition and
reward kernels, bounded mean reward and `0 < γ < 1`, there is a measurable map `π* : S → A` with
`π*(s) ∈ argmax_a Q*(s, a)` for every `s`.

**Formalization Note** The paper takes the existence of such a deterministic policy for granted;
measurability is what makes `π*` a policy (a Dirac kernel). The mean reward is bounded, which the
paper's `‖Q*‖_∞ ≤ Q_max` implies. -/
theorem exists_measurable_greedy {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    [Fintype A] [Nonempty A] [MeasurableSingletonClass A]
    (M : MDP S A) [IsMarkovKernel M.P] [IsMarkovKernel M.Rw]
    (hr : ∃ R : ℝ, ∀ x, |M.meanReward x| ≤ R)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ∃ πs : S → A, Measurable πs ∧ IsGreedy (QStar M γ) πs := by sorry

end OfflineRLFastRates
