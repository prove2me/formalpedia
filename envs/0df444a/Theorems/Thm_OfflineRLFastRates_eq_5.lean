-- Prove2me | Theorems.Thm_OfflineRLFastRates_eq_5
-- name    : OfflineRLFastRates.eq_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:27:41.807283+00:00
-- url     : https://prove2.me/theorems/a5d17a62-f6d2-4a8c-9a7d-e1b044462def
-- title:
--   Eq. (5) — peeling: $\mathbb E_{d^{\pi}}[Q^*(s,\pi^*(s))-Q^*(s,\pi(s))]\le2a_n\sum_{i=0}^{i_{\max}}2^iP(B_i)+2Q_{\max}P(B')$ (corrected: $2Q_{\max}$)
-- statement:
--   Consider a discounted MDP on a measurable state space $\mathcal S$ with a finite nonempty action set $\mathcal A$, Markov transition and reward kernels, a bounded mean reward, $0<\gamma<1$ and an initial distribution $\mu$, and suppose $\|Q^*\|_\infty\le Q_{\max}$. Let $\pi$ be a measurable deterministic policy with occupancy distribution $d^\pi$, let $\pi^*$ be greedy for $Q^*$, let $g(s)=Q^*(s,\pi^*(s))-Q^*(s,\pi(s))$, $a_n>0$ and $i_{\max}\in\mathbb N$, and define the events
--   $$B_0=\{0<g\le2a_n\},\qquad B_i=\{2^ia_n<g\le2^{i+1}a_n\}\ (i\ge1),\qquad B'=\{2^{i_{\max}+1}a_n<g\}.$$
--   Then
--   $$\mathbb E_{s\sim d^{\pi}}\big[g(s)\big]=\mathbb E_{s\sim d^{\pi}}\Big[\sum_{i=0}^{i_{\max}}g(s)\mathbb I\{B_i\}+g(s)\mathbb I\{B'\}\Big]\le2a_n\sum_{i=0}^{i_{\max}}2^i\,\mathbb P_{s\sim d^{\pi}}(B_i)+2Q_{\max}\,\mathbb P_{s\sim d^{\pi}}(B').$$
--
--   This is the peeling step of the proof of Theorem 1: it splits the expected $Q^*$-gap into dyadic shells, each weighted by its largest gap.
--
--   **Formalization Note** The probabilities are the (finite) masses of the events under $d^\pi$, as real numbers.
--
--   Differences from the source:
--   - correction: $Q_{\max}\,\mathbb P_{s\sim d^{\hat\pi}}(B')$ → $2Q_{\max}\,\mathbb P_{s\sim d^{\pi}}(B')$; reason: $\|Q^*\|_\infty\le Q_{\max}$ only bounds the gap by $2Q_{\max}$, and the printed display is false: one state with a self-loop, actions $1,2$ with $r(s,1)=(1-\gamma)Q_{\max}$, $r(s,2)=-(1+\gamma)Q_{\max}$ (so $Q^*(s,1)=Q_{\max}$, $Q^*(s,2)=-Q_{\max}$), $\pi\equiv2$, $a_n=Q_{\max}/4$, $i_{\max}=0$: the left side is $2Q_{\max}$ and the printed right side is $Q_{\max}$.
--   - generalization: the data-driven $\hat\pi$ for a fixed dataset, and a deterministic policy $\pi^*$ → every measurable deterministic $\pi$, and any (not necessarily measurable) $Q^*$-greedy selection $\pi^*$; reason: the inequality uses only that $\pi^*$ is greedy, and the source's $\hat\pi$, $\pi^*$ are instances.
--   - encoding: the mean reward $r(s,a)$ → bounded; reason: the source's $\|Q^*\|_\infty\le Q_{\max}$ forces a bounded $r$, and Lean's suprema, series and integrals need it to carry their values.
--   - encoding: policies $\pi(a\mid s)$, $\max_\pi$ and a finite action space → Markov kernels, suprema over them, and a finite nonempty type with measurable singletons; reason: Lean convention for the source's stationary stochastic policies; the maxima are attained, so the suprema are the same numbers, an MDP has at least one action, and a finite action space carries the discrete $\sigma$-algebra.
-- source:
--   Hu, Kallus, Uehara, Fast Rates for the Regret of Offline Reinforcement Learning, arXiv:2102.00479v2, §7.1, p.17, Eq. (5) (events B₀, Bᵢ, B′ defined on p.16)

import Mathlib
import Definitions.Def_OffPolicyDRL_CrossFit_MDP
import Definitions.Def_OfflineRLFastRates_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OfflineRLFastRates

open OffPolicyDRL.CrossFit

/-- Eq. (5), the peeling inequality, **corrected: `2Q_max`** (Hu, Kallus, Uehara, Fast Rates for
the Regret of Offline Reinforcement Learning, arXiv:2102.00479v2, §7.1, p.17; events on p.16).

Let `π` be a measurable deterministic policy, `π*` a `Q*`-greedy policy, `g(s) = Q*(s, π*(s)) −
Q*(s, π(s))`, `aₙ > 0`, `i_max ∈ ℕ`, and `‖Q*‖_∞ ≤ Q_max`. With `B₀ = {0 < g ≤ 2aₙ}`,
`Bᵢ = {2^i aₙ < g ≤ 2^{i+1} aₙ}` (`i ≥ 1`) and `B' = {2^{i_max+1} aₙ < g}`,
`E_{s∼d^π}[g(s)] = E_{s∼d^π}[∑_{i=0}^{i_max} g(s) I{Bᵢ} + g(s) I{B'}]
≤ 2aₙ ∑_{i=0}^{i_max} 2^i P_{s∼d^π}(Bᵢ) + 2 Q_max P_{s∼d^π}(B')`.

**Formalization Note** The paper prints `Q_max` in front of `P(B')`; the gap can be `2 Q_max` when
`Q*` takes both signs, so the printed display is false and `2 Q_max` is stated. The measures of
the events are `toReal` of the finite measure `d^π`. -/
theorem eq_5 {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    [Fintype A] [Nonempty A] [MeasurableSingletonClass A]
    (M : MDP S A) [IsMarkovKernel M.P] [IsMarkovKernel M.Rw]
    (hr : ∃ R : ℝ, ∀ x, |M.meanReward x| ≤ R)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (μ : Measure S) [IsProbabilityMeasure μ]
    (πs : S → A) (hgreedy : IsGreedy (QStar M γ) πs)
    (π : S → A) (hπ : Measurable π)
    (aₙ : ℝ) (haₙ : 0 < aₙ) (imax : ℕ) (Qmax : ℝ) (hQmax : ∀ x, |QStar M γ x| ≤ Qmax) :
    ∫ s, gapFun (QStar M γ) πs π s ∂(M.discVisitation γ μ (Kernel.deterministic π hπ)) =
      ∫ s, (∑ i ∈ Finset.range (imax + 1), gapFun (QStar M γ) πs π s *
            (peelEvent (gapFun (QStar M γ) πs π) aₙ i).indicator (fun _ => (1 : ℝ)) s +
          gapFun (QStar M γ) πs π s *
            (peelTail (gapFun (QStar M γ) πs π) aₙ imax).indicator (fun _ => (1 : ℝ)) s)
        ∂(M.discVisitation γ μ (Kernel.deterministic π hπ)) ∧
    ∫ s, gapFun (QStar M γ) πs π s ∂(M.discVisitation γ μ (Kernel.deterministic π hπ)) ≤
      2 * aₙ * ∑ i ∈ Finset.range (imax + 1), 2 ^ i *
          (M.discVisitation γ μ (Kernel.deterministic π hπ)
            (peelEvent (gapFun (QStar M γ) πs π) aₙ i)).toReal +
        2 * Qmax * (M.discVisitation γ μ (Kernel.deterministic π hπ)
            (peelTail (gapFun (QStar M γ) πs π) aₙ imax)).toReal := by sorry

end OfflineRLFastRates
