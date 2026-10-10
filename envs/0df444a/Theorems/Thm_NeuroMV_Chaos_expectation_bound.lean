-- Prove2me | Theorems.Thm_NeuroMV_Chaos_expectation_bound
-- name    : NeuroMV.Chaos.expectation_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:43:01.573431+00:00
-- url     : https://prove2.me/theorems/0b76e30c-0520-4477-9779-83e499f0402f
-- title:
--   §3, p. 21 — 𝓔[sup_{s≤T, r∈𝒜_N} 𝔼|X^{r,𝒜_N}_s − X̄^r_s|²] ≤ C(T) Σ_α(…), with C(T) finite and independent of ε and N
-- statement:
--   Assume Hypothesis 1.6 and the chaotic initial condition, and fix $T>0$. Suppose that for $\mathbb P'$-almost every disorder $\omega'$ the processes $X^{\mathcal A_N}(\omega')$ solve the network equation (1) for every $N$, $\hat X(\omega')$ solves (6) in $L^\infty([-\tau,T];L^2)$, and $\bar X(\omega')$ solves (5) for every neuron of $\bigcup_N\mathcal A_N$. Then there is a finite constant $C(T)$ such that for every $\varepsilon>0$ and every $N$,
--   $$\mathcal E\Big[\sup_{s\in[0,T],\,r\in\mathcal A_N}\mathbb E|X^{r,\mathcal A_N}_s-\bar X^r_s|^2\Big]\le C(T)\sum_{\alpha}\Big(\frac{\#\mathcal A_N\cap\Gamma_\alpha}{\mathcal S^2_{\mathcal A_N,\alpha}}+\varepsilon\frac{(\#\mathcal A_N\cap\Gamma_\alpha)^2}{\mathcal S^2_{\mathcal A_N,\alpha}}+M^{(\varepsilon)}_\alpha\sum_m\Big(\frac{\#\mathcal A_N\cap\Gamma^{m,\varepsilon}_\alpha}{\mathcal S_{\mathcal A_N,\alpha}}-\mathcal R(\Gamma^{m,\varepsilon}_\alpha)\Big)^2\Big),$$
--   where $\mathcal E$ is the expectation over the disorder.
--
--   Integrating the $\omega'$-wise Gronwall bound uses the exponential moment condition (H6); the uniformity of $C(T)$ in $\varepsilon$ and $N$ is what lets one first send $N\to\infty$ and then $\varepsilon\to0$.
--
--   **Formalization Note.** The constant is quantified before $\varepsilon$ and $N$. All quantities are in $[0,\infty]$; the outer integral is a lower Lebesgue integral over $\Omega'$.
-- source:
--   Mehri, Scheutzow, Stannat, Zangeneh, Propagation of Chaos for Stochastic Spatially Structured Neuronal Networks with Delay driven by Jump Diffusions, arXiv:1805.01654v3, §3, proof of Theorem 1.8, p. 21, second display

import Mathlib
import Definitions.Def_NeuroMV_Chaos_Network

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace NeuroMV.Chaos

/-- **The `𝓔`-integrated bound** (§3, p. 21). If for `ℙ'`-a.e. `ω'` the processes `X^{𝒜_N}(ω')`
solve (1) for every `N`, `X(ω')` solves (6) in `L^∞([-τ, T]; L²)` and `X̄(ω')` solves (5) for
every neuron of `⋃_N 𝒜_N`, then there is a finite constant `C(T)`, the same for every `ε > 0`
and every `N`, with
`𝓔[sup_{s ∈ [0,T], r ∈ 𝒜_N} 𝔼|X^{r,𝒜_N}_s − X̄^r_s|²]
  ≤ C(T) Σ_α (#𝒜_N ∩ Γ_α / 𝒮²_{𝒜_N,α} + ε (#𝒜_N ∩ Γ_α)² / 𝒮²_{𝒜_N,α}
      + M^{(ε)}_α Σ_m (#𝒜_N ∩ Γ^{m,ε}_α / 𝒮_{𝒜_N,α} − 𝓡(Γ^{m,ε}_α))²)`. -/
theorem expectation_bound
    {d m n k P : ℕ} {U Ω' Ω ΩX : Type*} [MeasurableSpace U] [MeasurableSpace Ω']
    [MeasurableSpace Ω] [MeasurableSpace ΩX]
    (G : Geometry k P) (ν : Measure U) [SigmaFinite ν] (Pr' : Measure Ω')
    [IsProbabilityMeasure Pr'] (C : Coeffs d m n k P U Ω') (R : Rates Ω')
    (pos : ℕ → NeuroMV.WellPosed.Pos k) (𝒜 : ℕ → Finset ℕ) (S : ℕ → Fin P → ℝ) (Q : Partitions k P)
    (Pr : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (W : ℕ → ℝ≥0 → Ω → EthierKurtz.SDEState m) (B : ℕ → Fin P → ℝ≥0 → Ω → EthierKurtz.SDEState n)
    (Nall : Ω → Set (ℝ≥0 × ((ℕ × Option (Fin P)) × U))) (z : ℕ → ℝ → Ω → EthierKurtz.SDEState d)
    (PrX : Measure ΩX) (𝓕X : Filtration ℝ≥0 ‹MeasurableSpace ΩX›)
    (WX : ℝ≥0 → ΩX → EthierKurtz.SDEState m) (BX : Fin P → ℝ≥0 → ΩX → EthierKurtz.SDEState n)
    (NX : ΩX → Set (ℝ≥0 × (Option (Fin P) × U))) (zh : Fin P → ℝ → ΩX → EthierKurtz.SDEState d)
    (hG : G.Valid) (hH : Hyp16 G ν C R pos 𝒜 S Pr' Q)
    (hnet : NetSetup G ν pos 𝒜 S Pr 𝓕 W B Nall z)
    (hnoise : IsNoise6 PrX 𝓕X ν WX BX NX) (hzh : IsInit PrX 𝓕X G.τ zh)
    (hchaos : ChaoticInit G pos 𝒜 Pr z PrX zh)
    (T : ℝ) (hT : 0 < T)
    (XN : ℕ → Ω' → ℕ → ℝ → Ω → EthierKurtz.SDEState d)
    (hXN : ∀ N, ∀ᵐ ω' ∂Pr', IsNetSol G ν C pos 𝒜 S Pr 𝓕 W B Nall z N ω' T (XN N ω'))
    (X : Ω' → NeuroMV.WellPosed.Pos k → ℝ → ΩX → EthierKurtz.SDEState d)
    (hX : ∀ᵐ ω' ∂Pr', IsStrongSol6 G ν C PrX 𝓕X WX BX NX zh ω' T (X ω') ∧
      InClass G PrX T (X ω'))
    (Xbar : Ω' → ℕ → ℝ → Ω → EthierKurtz.SDEState d)
    (hXbar : ∀ᵐ ω' ∂Pr', ∀ i : ℕ, (∃ N, i ∈ 𝒜 N) →
      IsLimitSol G ν C pos Pr 𝓕 W B Nall z PrX (X ω') ω' T i (Xbar ω' i)) :
    ∃ CT : ℝ≥0∞, CT < ⊤ ∧ ∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
      ∫⁻ ω', (⨆ s ∈ Set.Icc (0 : ℝ) T, ⨆ i ∈ 𝒜 N,
          ∫⁻ ω, ‖XN N ω' i s ω - Xbar ω' i s ω‖ₑ ^ 2 ∂Pr) ∂Pr' ≤
        CT * ENNReal.ofReal (∑ α, bracket G pos 𝒜 S Q N ε α) := by sorry

end NeuroMV.Chaos
