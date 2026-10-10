-- Prove2me | Theorems.Thm_NeuroMV_Chaos_gronwall_bound
-- name    : NeuroMV.Chaos.gronwall_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:42:58.105262+00:00
-- url     : https://prove2.me/theorems/7afeeba5-77c8-44b9-a905-7f67c9d1edfb
-- title:
--   §3, p. 21 — Gronwall: sup_{s≤T, r∈𝒜_N} 𝔼|X^{r,𝒜_N}_s − X̄^r_s|² ≤ 36 Σ_α(…) C₂(T, ω′) exp[∫_0^T (L + 6L̄ Σ_α(#𝒜_N∩Γ_α)²/𝒮² + P)]
-- statement:
--   Assume Hypothesis 1.6 and the chaotic initial condition. Fix a disorder $\omega'$ at which $\hat X$ solves (6) in $L^\infty([-\tau,T];L^2)$, $\bar X$ solves (5) for every neuron of $\bigcup_N\mathcal A_N$, and $X^{\mathcal A_N}$ solves the network equation (1). Then for every $\varepsilon>0$,
--   $$\sup_{s\in[0,T],\,r\in\mathcal A_N}\mathbb E|X^{r,\mathcal A_N}_s-\bar X^r_s|^2\le 36\sum_{\alpha}\Big(\frac{\#\mathcal A_N\cap\Gamma_\alpha}{\mathcal S^2_{\mathcal A_N,\alpha}}+\varepsilon\frac{(\#\mathcal A_N\cap\Gamma_\alpha)^2}{\mathcal S^2_{\mathcal A_N,\alpha}}+M^{(\varepsilon)}_\alpha\sum_m\Big(\frac{\#\mathcal A_N\cap\Gamma^{m,\varepsilon}_\alpha}{\mathcal S_{\mathcal A_N,\alpha}}-\mathcal R(\Gamma^{m,\varepsilon}_\alpha)\Big)^2\Big)C_2(T,\omega')\exp\Big[\int_0^T\Big(L_s(\omega')+6\bar L_s(\omega')\sum_\alpha\frac{(\#\mathcal A_N\cap\Gamma_\alpha)^2}{\mathcal S^2_{\mathcal A_N,\alpha}}+P\Big)ds\Big].$$
--
--   This is the quantitative, $\omega'$-wise form of propagation of chaos: the distance between the network and its limit is controlled by the bracket, which becomes small as $N\to\infty$ and then $\varepsilon\to0$.
--
--   **Formalization Note.** This is the first inequality of the display on p. 21. The second inequality printed there (constant 144) omits the factor $\sup_{u,\zeta}\mathbb E|\hat z^\zeta(u)|^2+1$ of $C_1$ and is not posed. All quantities are in $[0,\infty]$.
-- source:
--   Mehri, Scheutzow, Stannat, Zangeneh, Propagation of Chaos for Stochastic Spatially Structured Neuronal Networks with Delay driven by Jump Diffusions, arXiv:1805.01654v3, §3, proof of Theorem 1.8, p. 21, first display (first inequality)

import Mathlib
import Definitions.Def_NeuroMV_Chaos_Network

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace NeuroMV.Chaos

/-- **The Gronwall bound** (§3, p. 21, first inequality). At a disorder `ω'` where `X` solves (6)
in `L^∞([-τ, T]; L²)`, `X̄` solves (5) for every neuron of `⋃_N 𝒜_N` and `X^{𝒜_N}` solves the
network equation (1), for every `ε > 0` (with the partition of Hypothesis 1.6):
`sup_{s ∈ [0,T], r ∈ 𝒜_N} 𝔼|X^{r,𝒜_N}_s − X̄^r_s|²
  ≤ 36 Σ_α (#𝒜_N ∩ Γ_α / 𝒮²_{𝒜_N,α} + ε (#𝒜_N ∩ Γ_α)² / 𝒮²_{𝒜_N,α}
      + M^{(ε)}_α Σ_m (#𝒜_N ∩ Γ^{m,ε}_α / 𝒮_{𝒜_N,α} − 𝓡(Γ^{m,ε}_α))²) C₂(T, ω')
    × exp[∫_0^T (L_s + 6 L̄_s Σ_α (#𝒜_N ∩ Γ_α)² / 𝒮²_{𝒜_N,α} + P) ds]`. -/
theorem gronwall_bound
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
    (ω' : Ω') (X : NeuroMV.WellPosed.Pos k → ℝ → ΩX → EthierKurtz.SDEState d)
    (hX : IsStrongSol6 G ν C PrX 𝓕X WX BX NX zh ω' T X) (hcl : InClass G PrX T X)
    (Xbar : ℕ → ℝ → Ω → EthierKurtz.SDEState d)
    (hXbar : ∀ i : ℕ, (∃ N, i ∈ 𝒜 N) → IsLimitSol G ν C pos Pr 𝓕 W B Nall z PrX X ω' T i (Xbar i))
    (N : ℕ) (XN : ℕ → ℝ → Ω → EthierKurtz.SDEState d)
    (hXN : IsNetSol G ν C pos 𝒜 S Pr 𝓕 W B Nall z N ω' T XN) :
    ∀ ε : ℝ, 0 < ε →
      (⨆ s ∈ Set.Icc (0 : ℝ) T, ⨆ i ∈ 𝒜 N, ∫⁻ ω, ‖XN i s ω - Xbar i s ω‖ₑ ^ 2 ∂Pr) ≤
        ENNReal.ofReal (36 * ∑ α, bracket G pos 𝒜 S Q N ε α) * C2 G R PrX zh T ω' *
          ENNReal.ofReal (Real.exp (∫ s in (0 : ℝ)..T,
            (R.L s.toNNReal ω' + 6 * R.Lb s.toNNReal ω' * sqSum G pos 𝒜 S N + P))) := by sorry

end NeuroMV.Chaos
