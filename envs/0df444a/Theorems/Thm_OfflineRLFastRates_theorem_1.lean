-- Prove2me | Theorems.Thm_OfflineRLFastRates_theorem_1
-- name    : OfflineRLFastRates.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:27:47.618573+00:00
-- url     : https://prove2.me/theorems/49aff174-edf1-4401-b06a-c86274137cdf
-- title:
--   Theorem 1 — under the margin condition, the greedy policy of $\hat f$ has regret $O(a_n^{1+\alpha})$ (corrected: uniform error bound)
-- statement:
--   Consider a discounted MDP on a measurable state space $\mathcal S$ with a finite nonempty action set $\mathcal A$, Markov transition and reward kernels, a bounded mean reward, a discount factor $0<\gamma<1$ and an initial distribution $\mu$; let $Q^*$, $V^*$ be the optimal $Q$-function and value, $\Delta$ the margin of $Q^*$, and $d^\pi$ the average state occupancy distribution of a policy $\pi$.
--
--   Let the data be a probability space $(\Omega,\mathbb P_{\mathcal D})$, let $\hat f_\omega$ be a data-driven estimate of $Q^*$, and let $\hat\pi_\omega=\pi_{\hat f_\omega}$ be any measurable greedy policy for $\hat f_\omega$ (any tie-breaking). Let $\Pi$ be a class of deterministic policies with $\hat\pi\in\Pi$ almost surely. Suppose
--
--   1. Condition 1 (margin): $\delta_0>0$, $\alpha\in[0,\infty]$, and $\sup_{\pi\in\Pi}\mathbb P_{s\sim d^\pi}(0<\Delta(s)\le\delta)\le(\delta/\delta_0)^\alpha$ for all $\delta>0$;
--   2. Condition 2, corrected (uniform error bound): $C>0$, $a_n>0$, and for every $\delta\ge a_n$ there is an event $E$ with $\mathbb P_{\mathcal D}(E)\le C\exp(-\delta^2/a_n^2)$ off which $|\hat f(s,a)-Q^*(s,a)|<\delta$ for every $\pi\in\Pi$, $d^\pi$-almost every $s$ and every $a$;
--   3. $\|Q^*\|_\infty\le Q_{\max}$.
--
--   Fix any $\delta_1\ge\delta_0$ with $\delta_1>2a_n$, and let $i_{\max}$ be the largest integer with $2^{i_{\max}+1}a_n<\delta_1$. Then
--   $$\mathbb E_{\mathcal D}\big[V^*-V^{\hat\pi}\big]\le\frac{1}{1-\gamma}\Big(2a_n\Big(\frac{2a_n}{\delta_0}\Big)^{\alpha}+\sum_{i=1}^{i_{\max}}C\exp\big(-2^{2i-2}\big)\,2^{i+2}a_n\Big(\frac{2^{i+1}a_n}{\delta_0}\Big)^{\alpha}\Big)+\frac{2Q_{\max}C}{1-\gamma}\exp\big(-\delta_1^2/(4a_n)^2\big),$$
--   where $x^\infty$ is $0$, $1$ or $\infty$ for $x<1$, $x=1$, $x>1$. For finite $\alpha$ the right side equals the printed bound
--   $$\frac{2^{\alpha+1}}{(1-\gamma)\delta_0^{\alpha}}\Big(1+C\sum_{i=1}^{i_{\max}}\exp\big(-2^{2i-2}\big)2^{(\alpha+1)i+1}\Big)a_n^{\alpha+1}+\frac{2Q_{\max}C}{1-\gamma}\exp\big(-\delta_1^2/(4a_n)^2\big).$$
--
--   This is the paper's main result: the regret of a greedy policy is the estimation rate $a_n$ raised to the power $1+\alpha$, so an $a_n=n^{-1/2}$ estimate gives regret $O(n^{-(1+\alpha)/2})$, faster than the usual $O(n^{-1/2})$ whenever $\alpha>0$.
--
--   **Formalization Note** $V^*$ and $Q^*$ are suprema over Markov policies, and $V^{\hat\pi}=\mathbb E_{s_0\sim\mu}V^{\hat\pi}(s_0)$. The regret is the lower Lebesgue integral of the nonnegative part of $V^*-V^{\hat\pi}$ and the bound is in $[0,\infty]$, written in the factored form above.
--
--   Differences from the source:
--   - correction: Condition 2 (Eq. (2)), a tail bound at each $(s,a)$ separately → one event $E$ for each $\delta\ge a_n$, with $\mathbb P_{\mathcal D}(E)\le C e^{-\delta^2/a_n^2}$, off which every action at $d^\pi$-almost every state of every $\pi\in\Pi$ has error $<\delta$; reason: the printed theorem is false: a root with $N=\lceil1/p\rceil$ actions leading to absorbing leaves whose estimates err independently with probability $p=e^{-1.01^2/a_n^2}$, and a greedy $\hat\pi$ that steers into an erroneous leaf, satisfy every hypothesis (pointwise Condition 2 with $C=1$, Condition 1 with $\delta_0=1$, $\alpha=1$), yet the regret is at least $1-1/e\approx0.632$ while the bound is $0.378$ at $a_n=0.1$ ($\delta_1=1$).
--   - reading: the printed bound $2^{\alpha+1}a_n^{\alpha+1}/\delta_0^{\alpha}\cdots$, undefined at $\alpha=\infty$ → the factored form $2a_n(2a_n/\delta_0)^\alpha+\sum_iC e^{-2^{2i-2}}2^{i+2}a_n(2^{i+1}a_n/\delta_0)^\alpha$ in $[0,\infty]$ with the $x^\infty$ convention of Condition 1; reason: equal to the printed bound term by term for every finite $\alpha$, and at $\alpha=\infty$ it is what the source's own convention gives.
--   - generalization: the data $\mathcal D$ of $n$ iid transitions → an arbitrary probability space $(\Omega,\mathbb P_{\mathcal D})$; reason: Theorem 1 never uses the sampling scheme, and the iid sample is an instance.
--   - generalization: expectations over $\mathcal D$ that presuppose measurability of $\hat f$ and $\hat\pi$ in the data → no measurability in $\omega$ is assumed; reason: the bound holds outcome by outcome off the events $E$, so neither they nor the estimates need be measurable; for a non-measurable integrand the Lean integral is the lower integral, and measurable estimates, where it is the expectation, are an instance.
--   - encoding: "$i_{\max}$ the largest integer with $2^{i_{\max}+1}a_n<\delta_1$" → $i_{\max}\in\mathbb N$ with $2^{i_{\max}+1}a_n<\delta_1\le2^{i_{\max}+2}a_n$; reason: the same number ($i_{\max}\ge0$ because $\delta_1>2a_n$).
--   - encoding: $\mathbb E_{\mathcal D}[V^*-V^{\hat\pi}]$ → the lower Lebesgue integral of $\max(V^*-V^{\hat\pi},0)$; reason: $V^*\ge V^{\hat\pi}$, so the value is the same whenever the expectation exists.
--   - encoding: a class $\Pi\subseteq[\mathcal S\to\mathcal A]$, deterministic policies $\hat\pi$, and $\sup_{\pi\in\Pi}$ in Condition 1 → a set of measurable maps, a measurable map for each $\omega$, and the bound of Condition 1 for each $\pi\in\Pi$; reason: a deterministic policy must be measurable for $d^\pi$ and $V^\pi$ to exist, and a supremum is at most a bound exactly when every member is.
--   - encoding: the mean reward $r(s,a)$ → bounded; reason: $\|Q^*\|_\infty\le Q_{\max}$ forces a bounded $r$, which Lean's suprema and series need to carry their values; without it they return junk values.
--   - encoding: policies $\pi(a\mid s)$, $\max_\pi$ and a finite action space → Markov kernels, suprema over them, and a finite nonempty type with measurable singletons; reason: Lean convention for the source's stationary stochastic policies; the maxima are attained, so the suprema are the same numbers, an MDP has at least one action, and a finite action space carries the discrete $\sigma$-algebra.
-- source:
--   Hu, Kallus, Uehara, Fast Rates for the Regret of Offline Reinforcement Learning, arXiv:2102.00479v2, §2, pp.6–7, Theorem 1 (Condition 1, p.6; Condition 2, p.6, corrected; proof pp.16–18)

import Mathlib
import Definitions.Def_OffPolicyDRL_CrossFit_MDP
import Definitions.Def_OfflineRLFastRates_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OfflineRLFastRates

open OffPolicyDRL.CrossFit

/-- Theorem 1 (Hu, Kallus, Uehara, Fast Rates for the Regret of Offline Reinforcement Learning,
arXiv:2102.00479v2, §2, pp.6–7), **corrected: uniform error bound**.

Let a data-driven `f̂` be given and let `Π` be a class of deterministic policies such that the
greedy policy `π̂ = π_{f̂}` lies in `Π` almost surely. Suppose Condition 1 holds with `(δ₀, α)`, the
corrected Condition 2 holds with `(C, aₙ)`, and `‖Q*‖_∞ ≤ Q_max`. Fix any `δ₁ ≥ δ₀` with
`δ₁ > 2aₙ`, and let `i_max` be the largest integer with `2^{i_max+1}aₙ < δ₁`. Then
`E_D[V* − V^{π̂}] ≤ (1 − γ)⁻¹ (2aₙ (2aₙ/δ₀)^α + ∑_{i=1}^{i_max} C exp(−2^{2i−2}) 2^{i+2} aₙ
(2^{i+1}aₙ/δ₀)^α) + 2 Q_max C/(1 − γ) · exp(−δ₁²/(4aₙ)²)`, which for finite `α` is the printed
`2^{α+1}/((1 − γ)δ₀^α) (1 + C ∑_{i=1}^{i_max} exp(−2^{2i−2}) 2^{(α+1)i+1}) aₙ^{α+1}
+ 2 Q_max C/(1 − γ) exp(−δ₁²/(4aₙ)²)`.

**Formalization Note**
* The data is an arbitrary probability space `(Ω, P_D)`; `f̂ ω` and `π̂ ω` are the estimate and the
  greedy policy computed from the outcome `ω`. Any tie-breaking is allowed: `π̂ ω` is any
  measurable selection from `argmax_a f̂ ω (s, a)`.
* Policies are Markov kernels; `V*` and `Q*` are suprema over them. `V^{π̂}` is `∫ V^{π̂}(s) dµ`.
* The regret `E_D[V* − V^{π̂}]` is the lower Lebesgue integral of `ofReal(V* − V^{π̂ ω})`, and the
  bound is in `ℝ≥0∞`, in the factored form above; `x^α` is `marginPow` (the paper's `x^∞`
  convention at `α = ∞`).
* `i_max` is encoded by `2^{i_max+1}aₙ < δ₁ ≤ 2^{i_max+2}aₙ`.
* The mean reward is bounded. -/
theorem theorem_1 {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    [Fintype A] [Nonempty A] [MeasurableSingletonClass A]
    (M : MDP S A) [IsMarkovKernel M.P] [IsMarkovKernel M.Rw]
    (hr : ∃ R : ℝ, ∀ x, |M.meanReward x| ≤ R)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (μ : Measure S) [IsProbabilityMeasure μ]
    (Pclass : Set (DetPolicy S A)) (δ₀ : ℝ) (α : ℝ≥0∞)
    (hmargin : MarginCondition M γ μ Pclass δ₀ α)
    {Ω : Type*} [MeasurableSpace Ω] (P_D : Measure Ω) [IsProbabilityMeasure P_D]
    (fhat : Ω → S × A → ℝ) (C aₙ : ℝ) (herr : UniformErrorBound M γ μ Pclass P_D fhat C aₙ)
    (πhat : Ω → S → A) (hπhat : ∀ ω, Measurable (πhat ω))
    (hπgreedy : ∀ ω, IsGreedy (fhat ω) (πhat ω))
    (hmem : ∀ᵐ ω ∂P_D, (⟨πhat ω, hπhat ω⟩ : DetPolicy S A) ∈ Pclass)
    (Qmax : ℝ) (hQmax : ∀ x, |QStar M γ x| ≤ Qmax)
    (δ₁ : ℝ) (hδ₁₀ : δ₀ ≤ δ₁) (hδ₁ : 2 * aₙ < δ₁) (imax : ℕ)
    (himax : 2 ^ (imax + 1) * aₙ < δ₁ ∧ δ₁ ≤ 2 ^ (imax + 2) * aₙ) :
    ∫⁻ ω, ENNReal.ofReal
        (VStar M γ μ - policyValue M γ μ (Kernel.deterministic (πhat ω) (hπhat ω))) ∂P_D ≤
      ENNReal.ofReal ((1 - γ)⁻¹) *
          (ENNReal.ofReal (2 * aₙ) * marginPow α (2 * aₙ / δ₀) +
            ∑ i ∈ Finset.Icc 1 imax,
              ENNReal.ofReal (C * Real.exp (-((2 : ℝ) ^ (2 * i - 2))) * 2 ^ (i + 2) * aₙ) *
                marginPow α (2 ^ (i + 1) * aₙ / δ₀)) +
        ENNReal.ofReal (2 * Qmax * C / (1 - γ) * Real.exp (-(δ₁ ^ 2 / (4 * aₙ) ^ 2))) := by sorry

end OfflineRLFastRates
