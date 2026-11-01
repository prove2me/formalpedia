-- Prove2me | Theorems.Thm_OfflineRLFastRates_b0_bound
-- name    : OfflineRLFastRates.b0_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:27:39.79993+00:00
-- url     : https://prove2.me/theorems/d73539a8-f90d-44aa-bbe5-7a44c090c88b
-- title:
--   p.17 — bound on $B_0$: $\mathbb E_{\mathcal D}\mathbb E_{s\sim d^{\hat\pi}}[\mathbb I\{B_0\}]\le(2a_n/\delta_0)^\alpha$
-- statement:
--   Consider a discounted MDP on a measurable state space $\mathcal S$ with a finite nonempty action set $\mathcal A$, Markov transition and reward kernels, $0<\gamma<1$ and an initial distribution $\mu$. Let $\Pi$ be a class of deterministic policies satisfying Condition 1 (margin) with constants $\delta_0>0$ and $\alpha\in[0,\infty]$. Let the data be a probability space $(\Omega,\mathbb P_{\mathcal D})$ and $\hat\pi_\omega$ a measurable deterministic policy for each outcome $\omega$, with $\hat\pi\in\Pi$ almost surely. Let $\pi^*$ be greedy for $Q^*$, $a_n>0$, and $B_0(\omega)=\{s:0<Q^*(s,\pi^*(s))-Q^*(s,\hat\pi_\omega(s))\le2a_n\}$. Then
--   $$\mathbb E_{\mathcal D}\big[\mathbb P_{s\sim d^{\hat\pi}}(B_0)\big]\le\sup_{\pi\in\Pi}\mathbb P_{s\sim d^\pi}\big(0<\Delta(s)\le2a_n\big)\le\Big(\frac{2a_n}{\delta_0}\Big)^{\alpha},$$
--   which for finite $\alpha$ is $2^\alpha a_n^\alpha/\delta_0^\alpha$, and for $\alpha=\infty$ uses the convention $x^\infty\in\{0,1,\infty\}$ of Condition 1.
--
--   This controls the innermost shell of the peeling argument by the margin condition alone; no estimation error enters.
--
--   **Formalization Note** $\mathbb E_{\mathcal D}$ is the lower Lebesgue integral over $(\Omega,\mathbb P_{\mathcal D})$, valued in $[0,\infty]$.
--
--   Differences from the source:
--   - generalization: the data $\mathcal D$ of $n$ iid transitions → an arbitrary probability space $(\Omega,\mathbb P_{\mathcal D})$; reason: the bound never uses the sampling scheme, and the iid sample is an instance.
--   - generalization: a deterministic policy $\pi^*$ → any (not necessarily measurable) $Q^*$-greedy selection; reason: only greediness is used, and the source's $\pi^*$ is an instance.
--   - reading: $2^\alpha a_n^\alpha/\delta_0^\alpha$, undefined at $\alpha=\infty$ → $(2a_n/\delta_0)^\alpha$ with the $x^\infty$ convention of Condition 1; reason: equal for finite $\alpha$, and at $\alpha=\infty$ it is the source's own convention applied to the middle term $\sup_\pi\mathbb P(0<\Delta\le2a_n)\le(2a_n/\delta_0)^\alpha$.
--   - encoding: $\mathbb E_{\mathcal D}$ → the lower Lebesgue integral in $[0,\infty]$; reason: the integrand is a probability, so the value is the same whenever the expectation exists.
--   - encoding: a class $\Pi\subseteq[\mathcal S\to\mathcal A]$, deterministic policies $\hat\pi$, and $\sup_{\pi\in\Pi}$ in Condition 1 → a set of measurable maps, a measurable map for each $\omega$, and the bound of Condition 1 for each $\pi\in\Pi$; reason: a deterministic policy must be measurable for $d^\pi$ and $V^\pi$ to exist, and a supremum is at most a bound exactly when every member is.
--   - encoding: policies $\pi(a\mid s)$, $\max_\pi$ and a finite action space → Markov kernels, suprema over them, and a finite nonempty type with measurable singletons; reason: Lean convention for the source's stationary stochastic policies; the maxima are attained, so the suprema are the same numbers, an MDP has at least one action, and a finite action space carries the discrete $\sigma$-algebra.
-- source:
--   Hu, Kallus, Uehara, Fast Rates for the Regret of Offline Reinforcement Learning, arXiv:2102.00479v2, §7.1, p.17 (bound on B₀, "First of all, by Condition 1")

import Mathlib
import Definitions.Def_OffPolicyDRL_CrossFit_MDP
import Definitions.Def_OfflineRLFastRates_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OfflineRLFastRates

open OffPolicyDRL.CrossFit

/-- The bound on `B₀` (Hu, Kallus, Uehara, Fast Rates for the Regret of Offline Reinforcement
Learning, arXiv:2102.00479v2, §7.1, p.17: "`E_D E_{s∼d^π̂}[I{B₀}] ≤ sup_π P_{s∼d^π}(0 < Δ(s) ≤ 2aₙ)
≤ 2^α aₙ^α / δ₀^α`").

Under Condition 1 for `(Π, δ₀, α)`, for a data-driven measurable deterministic policy `π̂` with
`π̂ ∈ Π` almost surely, a `Q*`-greedy `π*` and `aₙ > 0`,
`E_D[d^{π̂}(B₀)] ≤ sup_{π ∈ Π} P_{s∼d^π}(0 < Δ(s) ≤ 2aₙ) ≤ (2aₙ/δ₀)^α`, where
`B₀ = {0 < Q*(s, π*(s)) − Q*(s, π̂(s)) ≤ 2aₙ}`.

**Formalization Note** The data is a probability space `(Ω, P_D)`; `E_D` is a lower Lebesgue
integral in `ℝ≥0∞`. The page's `sup_π` is the supremum over `Π`, in `ℝ≥0∞`. `(2aₙ/δ₀)^α` is `marginPow α (2aₙ/δ₀)`, which equals `2^α aₙ^α/δ₀^α` for
finite `α` and follows the paper's `x^∞` convention at `α = ∞`. -/
theorem b0_bound {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    [Fintype A] [Nonempty A] [MeasurableSingletonClass A]
    (M : MDP S A) [IsMarkovKernel M.P] [IsMarkovKernel M.Rw]
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (μ : Measure S) [IsProbabilityMeasure μ]
    (Pclass : Set (DetPolicy S A)) (δ₀ : ℝ) (α : ℝ≥0∞)
    (hmargin : MarginCondition M γ μ Pclass δ₀ α)
    {Ω : Type*} [MeasurableSpace Ω] (P_D : Measure Ω) [IsProbabilityMeasure P_D]
    (πhat : Ω → S → A) (hπhat : ∀ ω, Measurable (πhat ω))
    (hmem : ∀ᵐ ω ∂P_D, (⟨πhat ω, hπhat ω⟩ : DetPolicy S A) ∈ Pclass)
    (πs : S → A) (hgreedy : IsGreedy (QStar M γ) πs) (aₙ : ℝ) (haₙ : 0 < aₙ) :
    ∫⁻ ω, M.discVisitation γ μ (Kernel.deterministic (πhat ω) (hπhat ω))
        (peelEvent (gapFun (QStar M γ) πs (πhat ω)) aₙ 0) ∂P_D ≤
      ⨆ π ∈ Pclass, M.discVisitation γ μ (DetPolicy.kernel π)
        {s | 0 < margin (QStar M γ) s ∧ margin (QStar M γ) s ≤ 2 * aₙ} ∧
    (⨆ π ∈ Pclass, M.discVisitation γ μ (DetPolicy.kernel π)
        {s | 0 < margin (QStar M γ) s ∧ margin (QStar M γ) s ≤ 2 * aₙ}) ≤
      marginPow α (2 * aₙ / δ₀) := by sorry

end OfflineRLFastRates
