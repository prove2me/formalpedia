-- Prove2me | Theorems.Thm_OfflineRLFastRates_btail_bound
-- name    : OfflineRLFastRates.btail_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:27:31.289507+00:00
-- url     : https://prove2.me/theorems/bdcbf1a9-e289-47ca-a23d-d950ff479d16
-- title:
--   p.18 — bound on $B'$: $\mathbb E_{\mathcal D}\mathbb E_{s\sim d^{\hat\pi}}[\mathbb I\{B'\}]\le C\exp(-\delta_1^2/(4a_n)^2)$ (corrected: uniform error bound)
-- statement:
--   Consider a discounted MDP on a measurable state space $\mathcal S$ with a finite nonempty action set $\mathcal A$, Markov transition and reward kernels, $0<\gamma<1$ and an initial distribution $\mu$. Let $\Pi$ be a class of deterministic policies, the data a probability space $(\Omega,\mathbb P_{\mathcal D})$, $\hat f_\omega$ an estimate of $Q^*$ satisfying the corrected Condition 2 (uniform error bound) with $C>0$, $a_n>0$, and $\hat\pi_\omega$ a measurable deterministic policy greedy for $\hat f_\omega$ for every $\omega$, with $\hat\pi\in\Pi$ almost surely. Let $\pi^*$ be greedy for $Q^*$, let $\delta_1>2a_n$, and let $i_{\max}$ be the largest integer with $2^{i_{\max}+1}a_n<\delta_1$. Then, with $B'=\{2^{i_{\max}+1}a_n<Q^*(s,\pi^*(s))-Q^*(s,\hat\pi(s))\}$,
--   $$\mathbb E_{\mathcal D}\big[\mathbb P_{s\sim d^{\hat\pi}}(B')\big]\le C\exp\big(-2^{2i_{\max}}\big)\le C\exp\big(-\delta_1^2/(4a_n)^2\big).$$
--
--   The outermost shell, where the $Q^*$-gap exceeds $2^{i_{\max}+1}a_n$, has exponentially small mass; combined with the gap bound $2Q_{\max}$ it gives the last term of Theorem 1.
--
--   **Formalization Note** $\mathbb E_{\mathcal D}$ is the lower Lebesgue integral over $(\Omega,\mathbb P_{\mathcal D})$, valued in $[0,\infty]$.
--
--   Differences from the source:
--   - correction: Condition 2 (Eq. (2)) at each $(s,a)$ separately → one event $E$ for each $\delta\ge a_n$, with $\mathbb P_{\mathcal D}(E)\le Ce^{-\delta^2/a_n^2}$, off which every action at $d^\pi$-almost every state of every $\pi\in\Pi$ has error $<\delta$; reason: with the pointwise condition the display is false, because $\hat\pi$ depends on the data: in the root-and-leaves counterexample (independent leaf errors of probability $p=e^{-1.01^2/a_n^2}$, $N=\lceil1/p\rceil$ leaves, $\hat\pi$ steering into an erroneous leaf, $\delta_1=1$, $a_n=0.1$) the left side is about $0.316>2e^{-6.25}$.
--   - generalization: $2C\exp(-2^{2i_{\max}})\le2C\exp(-\delta_1^2/(4a_n)^2)$ → the same chain with $C$ in place of $2C$; reason: a stronger conclusion that specializes to the printed one since $C\le2C$; the uniform event gives it directly, and it is what makes the corrected Eq. (5) compose to Theorem 1's printed constant $2Q_{\max}C/(1-\gamma)$.
--   - generalization: the data $\mathcal D$ of $n$ iid transitions → an arbitrary probability space; a deterministic $\pi^*$ → any $Q^*$-greedy selection; reason: neither the sampling scheme nor the measurability of $\pi^*$ is used.
--   - encoding: "$i_{\max}$ the largest integer with $2^{i_{\max}+1}a_n<\delta_1$" → $i_{\max}\in\mathbb N$ with $2^{i_{\max}+1}a_n<\delta_1\le2^{i_{\max}+2}a_n$; reason: the same number ($i_{\max}\ge0$ because $\delta_1>2a_n$).
--   - encoding: $\mathbb E_{\mathcal D}$ → the lower Lebesgue integral in $[0,\infty]$; reason: the integrand is a probability, so the value is the same whenever the expectation exists.
--   - encoding: a class $\Pi\subseteq[\mathcal S\to\mathcal A]$, deterministic policies $\hat\pi$, and $\sup_{\pi\in\Pi}$ in Condition 1 → a set of measurable maps, a measurable map for each $\omega$, and the bound of Condition 1 for each $\pi\in\Pi$; reason: a deterministic policy must be measurable for $d^\pi$ and $V^\pi$ to exist, and a supremum is at most a bound exactly when every member is.
--   - encoding: policies $\pi(a\mid s)$, $\max_\pi$ and a finite action space → Markov kernels, suprema over them, and a finite nonempty type with measurable singletons; reason: Lean convention for the source's stationary stochastic policies; the maxima are attained, so the suprema are the same numbers, an MDP has at least one action, and a finite action space carries the discrete $\sigma$-algebra.
-- source:
--   Hu, Kallus, Uehara, Fast Rates for the Regret of Offline Reinforcement Learning, arXiv:2102.00479v2, §7.1, p.18 (bound on B′, "by Eq. (2) we have"); Condition 2, p.6 (corrected); i_max as in Theorem 1, p.7

import Mathlib
import Definitions.Def_OffPolicyDRL_CrossFit_MDP
import Definitions.Def_OfflineRLFastRates_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OfflineRLFastRates

open OffPolicyDRL.CrossFit

/-- The bound on `B'` (Hu, Kallus, Uehara, Fast Rates for the Regret of Offline Reinforcement
Learning, arXiv:2102.00479v2, §7.1, p.18: "`E_D E_{s∼d^π̂}[I{B'}] ≤ … ≤ 2C exp(−2^{2 i_max}) ≤
2C exp(−δ₁²/(4aₙ)²)`"), **corrected: uniform error bound**, with the constant `C` in place of the
printed `2C`.

Assume the corrected Condition 2 for `(f̂, C, aₙ)`, that `π̂(ω)` is a measurable `f̂(ω)`-greedy
policy for every outcome `ω`, that `π̂ ∈ Π` almost surely, that `π*` is `Q*`-greedy, and let
`δ₁ > 2aₙ` and `i_max` be the largest integer with `2^{i_max+1}aₙ < δ₁`. Then, for
`B' = {2^{i_max+1}aₙ < Q*(s, π*(s)) − Q*(s, π̂(s))}`,
`E_D[d^{π̂}(B')] ≤ C exp(−2^{2 i_max})` and `C exp(−2^{2 i_max}) ≤ C exp(−δ₁²/(4aₙ)²)`.

**Formalization Note** `i_max` is encoded by `2^{i_max+1}aₙ < δ₁ ≤ 2^{i_max+2}aₙ`, which
determines it uniquely. `E_D` is a lower Lebesgue integral in `ℝ≥0∞` over `(Ω, P_D)`. -/
theorem btail_bound {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    [Fintype A] [Nonempty A] [MeasurableSingletonClass A]
    (M : MDP S A) [IsMarkovKernel M.P] [IsMarkovKernel M.Rw]
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (μ : Measure S) [IsProbabilityMeasure μ]
    (Pclass : Set (DetPolicy S A))
    {Ω : Type*} [MeasurableSpace Ω] (P_D : Measure Ω) [IsProbabilityMeasure P_D]
    (fhat : Ω → S × A → ℝ) (C aₙ : ℝ) (herr : UniformErrorBound M γ μ Pclass P_D fhat C aₙ)
    (πhat : Ω → S → A) (hπhat : ∀ ω, Measurable (πhat ω))
    (hπgreedy : ∀ ω, IsGreedy (fhat ω) (πhat ω))
    (hmem : ∀ᵐ ω ∂P_D, (⟨πhat ω, hπhat ω⟩ : DetPolicy S A) ∈ Pclass)
    (πs : S → A) (hgreedy : IsGreedy (QStar M γ) πs)
    (δ₁ : ℝ) (hδ₁ : 2 * aₙ < δ₁) (imax : ℕ)
    (himax : 2 ^ (imax + 1) * aₙ < δ₁ ∧ δ₁ ≤ 2 ^ (imax + 2) * aₙ) :
    ∫⁻ ω, M.discVisitation γ μ (Kernel.deterministic (πhat ω) (hπhat ω))
        (peelTail (gapFun (QStar M γ) πs (πhat ω)) aₙ imax) ∂P_D ≤
      ENNReal.ofReal (C * Real.exp (-((2 : ℝ) ^ (2 * imax)))) ∧
    ENNReal.ofReal (C * Real.exp (-((2 : ℝ) ^ (2 * imax)))) ≤
      ENNReal.ofReal (C * Real.exp (-(δ₁ ^ 2 / (4 * aₙ) ^ 2))) := by sorry

end OfflineRLFastRates
