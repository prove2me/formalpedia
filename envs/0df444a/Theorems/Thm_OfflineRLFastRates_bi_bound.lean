-- Prove2me | Theorems.Thm_OfflineRLFastRates_bi_bound
-- name    : OfflineRLFastRates.bi_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:27:48.338339+00:00
-- url     : https://prove2.me/theorems/5b33bab8-18c1-411b-aa82-bd2856ae4460
-- title:
--   p.17 — bound on $B_i$: $\mathbb E_{\mathcal D}\mathbb E_{s\sim d^{\hat\pi}}[\mathbb I\{B_i\}]\le2Ce^{-2^{2i-2}}(2^{i+1}a_n/\delta_0)^\alpha$ (corrected: uniform error bound)
-- statement:
--   Consider a discounted MDP on a measurable state space $\mathcal S$ with a finite nonempty action set $\mathcal A$, Markov transition and reward kernels, $0<\gamma<1$ and an initial distribution $\mu$. Let $\Pi$ be a class of deterministic policies satisfying Condition 1 with $\delta_0>0$, $\alpha\in[0,\infty]$. Let the data be a probability space $(\Omega,\mathbb P_{\mathcal D})$, $\hat f_\omega$ an estimate of $Q^*$ satisfying the corrected Condition 2 (uniform error bound) with $C>0$, $a_n>0$, and $\hat\pi_\omega$ a measurable deterministic policy greedy for $\hat f_\omega$ for every $\omega$, with $\hat\pi\in\Pi$ almost surely. Let $\pi^*$ be greedy for $Q^*$. Then for every $i\ge1$, with $B_i=\{2^ia_n<Q^*(s,\pi^*(s))-Q^*(s,\hat\pi(s))\le2^{i+1}a_n\}$,
--   $$\mathbb E_{\mathcal D}\big[\mathbb P_{s\sim d^{\hat\pi}}(B_i)\big]\le2C\exp\big(-2^{2i-2}\big)\sup_{\pi\in\Pi}\mathbb P_{s\sim d^\pi}\big(0<\Delta(s)\le2^{i+1}a_n\big)\le2C\exp\big(-2^{2i-2}\big)\Big(\frac{2^{i+1}a_n}{\delta_0}\Big)^{\alpha}.$$
--
--   The $i$-th shell of the peeling argument has mass that decays doubly exponentially in $i$ (from the error bound) times the margin mass at scale $2^{i+1}a_n$.
--
--   **Formalization Note** $\mathbb E_{\mathcal D}$ is the lower Lebesgue integral over $(\Omega,\mathbb P_{\mathcal D})$, valued in $[0,\infty]$; the power uses the $x^\infty$ convention of Condition 1.
--
--   Differences from the source:
--   - correction: Condition 2 (Eq. (2)) at each $(s,a)$ separately → one event $E$ for each $\delta\ge a_n$, with $\mathbb P_{\mathcal D}(E)\le C e^{-\delta^2/a_n^2}$, off which every action at $d^\pi$-almost every state of every $\pi\in\Pi$ has error $<\delta$; reason: with the pointwise condition the bound is false, because $\hat\pi$ depends on the data: take a root with $N=\lceil1/p\rceil$ actions leading to absorbing leaves whose estimates err independently with probability $p=e^{-1.01^2/a_n^2}$, and let $\hat\pi$ steer into an erroneous leaf; every pointwise bound holds with $C=1$ ($\delta_0=1$, $\alpha=1$), and at $a_n=0.1$ the leaf gap $1$ lies in $B_3$, so $\mathbb E_{\mathcal D}[\mathbb P_{s\sim d^{\hat\pi}}(B_3)]\approx\tfrac12(1-1/e)\approx0.316$, while the right side is $2e^{-16}\cdot1.6<10^{-6}$.
--   - generalization: $i\in[1,i_{\max}]$ → every $i\ge1$; reason: the bound does not involve $i_{\max}$, and the source's range is included.
--   - generalization: the data $\mathcal D$ of $n$ iid transitions → an arbitrary probability space; a deterministic $\pi^*$ → any $Q^*$-greedy selection; reason: neither the sampling scheme nor the measurability of $\pi^*$ is used, and the source's objects are instances.
--   - reading: $(2^{i+1}a_n/\delta_0)^\alpha$ at $\alpha=\infty$ → the $x^\infty$ convention of Condition 1; reason: it is the convention under which the source's Condition 1 is stated.
--   - encoding: $\mathbb E_{\mathcal D}$ → the lower Lebesgue integral in $[0,\infty]$; reason: the integrand is a probability, so the value is the same whenever the expectation exists.
--   - encoding: a class $\Pi\subseteq[\mathcal S\to\mathcal A]$, deterministic policies $\hat\pi$, and $\sup_{\pi\in\Pi}$ in Condition 1 → a set of measurable maps, a measurable map for each $\omega$, and the bound of Condition 1 for each $\pi\in\Pi$; reason: a deterministic policy must be measurable for $d^\pi$ and $V^\pi$ to exist, and a supremum is at most a bound exactly when every member is.
--   - encoding: policies $\pi(a\mid s)$, $\max_\pi$ and a finite action space → Markov kernels, suprema over them, and a finite nonempty type with measurable singletons; reason: Lean convention for the source's stationary stochastic policies; the maxima are attained, so the suprema are the same numbers, an MDP has at least one action, and a finite action space carries the discrete $\sigma$-algebra.
-- source:
--   Hu, Kallus, Uehara, Fast Rates for the Regret of Offline Reinforcement Learning, arXiv:2102.00479v2, §7.1, p.17 (bound on Bᵢ, "Then from Eq. (2) and Condition 1 we have for i ∈ [1, imax]"); Condition 2, p.6 (corrected)

import Mathlib
import Definitions.Def_OffPolicyDRL_CrossFit_MDP
import Definitions.Def_OfflineRLFastRates_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OfflineRLFastRates

open OffPolicyDRL.CrossFit

/-- The bound on `Bᵢ`, `i ≥ 1` (Hu, Kallus, Uehara, Fast Rates for the Regret of Offline
Reinforcement Learning, arXiv:2102.00479v2, §7.1, p.17: "`E_D E_{s∼d^π̂}[I{Bᵢ}] ≤
2C exp(−2^{2i−2}) sup_{π∈Π} P_{s∼d^π}(0 < Δ(s) ≤ 2^{i+1}aₙ) ≤ 2C exp(−2^{2i−2})(2^{i+1}aₙ/δ₀)^α`"),
**corrected: uniform error bound**.

Assume Condition 1 for `(Π, δ₀, α)`, the corrected Condition 2 for `(f̂, C, aₙ)`, that `π̂(ω)` is a
measurable `f̂(ω)`-greedy policy for every outcome `ω`, that `π̂ ∈ Π` almost surely, and that `π*`
is `Q*`-greedy. Then for every `i ≥ 1`,
`E_D[d^{π̂}(Bᵢ)] ≤ 2C exp(−2^{2i−2}) sup_{π ∈ Π} P_{s∼d^π}(0 < Δ(s) ≤ 2^{i+1}aₙ)
≤ 2C exp(−2^{2i−2}) (2^{i+1}aₙ/δ₀)^α`.

**Formalization Note** The paper states the bound for `i ∈ [1, i_max]`; it is stated for every
`i ≥ 1`. `E_D` is a lower Lebesgue integral in `ℝ≥0∞` over the data space `(Ω, P_D)`, and the
power is `marginPow` (the paper's `x^∞` convention at `α = ∞`). -/
theorem bi_bound {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    [Fintype A] [Nonempty A] [MeasurableSingletonClass A]
    (M : MDP S A) [IsMarkovKernel M.P] [IsMarkovKernel M.Rw]
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (μ : Measure S) [IsProbabilityMeasure μ]
    (Pclass : Set (DetPolicy S A)) (δ₀ : ℝ) (α : ℝ≥0∞)
    (hmargin : MarginCondition M γ μ Pclass δ₀ α)
    {Ω : Type*} [MeasurableSpace Ω] (P_D : Measure Ω) [IsProbabilityMeasure P_D]
    (fhat : Ω → S × A → ℝ) (C aₙ : ℝ) (herr : UniformErrorBound M γ μ Pclass P_D fhat C aₙ)
    (πhat : Ω → S → A) (hπhat : ∀ ω, Measurable (πhat ω))
    (hπgreedy : ∀ ω, IsGreedy (fhat ω) (πhat ω))
    (hmem : ∀ᵐ ω ∂P_D, (⟨πhat ω, hπhat ω⟩ : DetPolicy S A) ∈ Pclass)
    (πs : S → A) (hgreedy : IsGreedy (QStar M γ) πs) (i : ℕ) (hi : 1 ≤ i) :
    ∫⁻ ω, M.discVisitation γ μ (Kernel.deterministic (πhat ω) (hπhat ω))
        (peelEvent (gapFun (QStar M γ) πs (πhat ω)) aₙ i) ∂P_D ≤
      ENNReal.ofReal (2 * C * Real.exp (-((2 : ℝ) ^ (2 * i - 2)))) *
        ⨆ π ∈ Pclass, M.discVisitation γ μ (DetPolicy.kernel π)
          {s | 0 < margin (QStar M γ) s ∧ margin (QStar M γ) s ≤ 2 ^ (i + 1) * aₙ} ∧
    ENNReal.ofReal (2 * C * Real.exp (-((2 : ℝ) ^ (2 * i - 2)))) *
        (⨆ π ∈ Pclass, M.discVisitation γ μ (DetPolicy.kernel π)
          {s | 0 < margin (QStar M γ) s ∧ margin (QStar M γ) s ≤ 2 ^ (i + 1) * aₙ}) ≤
      ENNReal.ofReal (2 * C * Real.exp (-((2 : ℝ) ^ (2 * i - 2)))) *
        marginPow α (2 ^ (i + 1) * aₙ / δ₀) := by sorry

end OfflineRLFastRates
