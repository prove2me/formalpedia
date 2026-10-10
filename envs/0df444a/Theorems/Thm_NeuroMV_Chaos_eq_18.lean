-- Prove2me | Theorems.Thm_NeuroMV_Chaos_eq_18
-- name    : NeuroMV.Chaos.eq_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:42:53.65218+00:00
-- url     : https://prove2.me/theorems/640f4558-7b27-47a6-b017-18044d9e7824
-- title:
--   (18), p. 18 — 𝔼|X^{r,𝒜_N}_t − X̄^r_t|² is bounded by a Gronwall integral, the I-terms and the network Lipschitz term
-- statement:
--   Assume Hypothesis 1.6 and the chaotic initial condition. Fix a disorder $\omega'$ at which $\hat X$ solves (6) in $L^\infty([-\tau,T];L^2)$, $\bar X$ solves the mean-field equation (5) for every neuron of $\bigcup_N\mathcal A_N$, and $X^{\mathcal A_N}$ solves the network equation (1). Then for every neuron $r\in\mathcal A_N$ and every $t\in[0,T]$,
--   $$\begin{aligned}\mathbb E|X^{r,\mathcal A_N}_t-\bar X^r_t|^2\le{}&\int_0^t(L_s(\omega')+P)\,\mathbb E|X^{r,\mathcal A_N}_{s-}-\bar X^r_{s-}|^2ds+2\sum_{\Theta\in\{\theta,\beta\}}\sum_{\alpha}I^\Theta_\alpha+2\sum_\alpha I^\eta_\alpha\\&+2\sum_{\alpha}\int_0^t\bar L_s(\omega')\frac{\#\mathcal A_N\cap\Gamma_\alpha}{\mathcal S^2_{\mathcal A_N,\alpha}}\sum_{\tilde r\in\mathcal A_N\cap\Gamma_\alpha}\mathbb E\Big[|X^{r,\mathcal A_N}_{s-}-\bar X^r_{s-}|^2\\&\qquad+\int_{-\tau}^0\big(|X^{\tilde r,\mathcal A_N}_{(s+u)-}-\bar X^{\tilde r}_{(s+u)-}|^2+1_{u<0}|X^{\tilde r,\mathcal A_N}_{s+u}-\bar X^{\tilde r}_{s+u}|^2\big)\lambda(du)\Big]ds.\end{aligned}$$
--
--   This is the first estimate of the proof of Theorem 1.8, obtained from Itô's formula for $|X^{r,\mathcal A_N}-\bar X^r|^2$; it separates the self-consistent Lipschitz part from the fluctuation terms $I^\Theta_\alpha$, $I^\eta_\alpha$.
--
--   **Formalization Note.** All quantities are in $[0,\infty]$; the $ds$-integrals are lower Lebesgue integrals over $(0,t]$.
-- source:
--   Mehri, Scheutzow, Stannat, Zangeneh, Propagation of Chaos for Stochastic Spatially Structured Neuronal Networks with Delay driven by Jump Diffusions, arXiv:1805.01654v3, §3, proof of Theorem 1.8, (18), p. 18, with the definitions of I^θ_α, I^Θ_α, I^η_α, pp. 18–20

import Mathlib
import Definitions.Def_NeuroMV_Chaos_Network

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace NeuroMV.Chaos

/-- **Display (18)** (§3, p. 18). At a disorder `ω'` where `X` solves (6) in `L^∞([-τ, T]; L²)`,
`X̄` solves (5) for every neuron of `⋃_N 𝒜_N` and `X^{𝒜_N}` solves the network equation (1):
for every neuron `r = pos i` of `𝒜_N` and `t ∈ [0, T]`,
`𝔼|X^{r,𝒜_N}_t − X̄^r_t|² ≤ ∫_0^t (L_s + P) 𝔼|X^{r,𝒜_N}_{s−} − X̄^r_{s−}|² ds
  + 2 Σ_{Θ ∈ {θ,β}} Σ_α I^Θ_α + 2 Σ_α I^η_α
  + 2 Σ_α ∫_0^t L̄_s (#𝒜_N ∩ Γ_α / 𝒮²_{𝒜_N,α}) Σ_{r̃ ∈ 𝒜_N ∩ Γ_α} 𝔼[|X^{r,𝒜_N}_{s−} − X̄^r_{s−}|²
      + ∫_{-τ}^0 (|X^{r̃,𝒜_N}_{(s+u)−} − X̄^{r̃}_{(s+u)−}|² + 1_{u<0} |X^{r̃,𝒜_N}_{s+u} − X̄^{r̃}_{s+u}|²) λ(du)] ds`. -/
theorem eq_18
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
    ∀ i ∈ 𝒜 N, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ω, ‖XN i t ω - Xbar i t ω‖ₑ ^ 2 ∂Pr ≤
        (∫⁻ s in Set.Ioc (0 : ℝ) t, ENNReal.ofReal (R.L s.toNNReal ω' + P) *
            ∫⁻ ω, ‖lft (XN i) s ω - lft (Xbar i) s ω‖ₑ ^ 2 ∂Pr) +
          2 * ∑ α, (Iθ G C pos 𝒜 S Pr Xbar PrX X ω' N α i t +
            Iβ G C pos 𝒜 S Pr Xbar PrX X ω' N α i t) +
          2 * ∑ α, Iη G ν C pos 𝒜 S Pr Xbar PrX X ω' N α i t +
          2 * ∑ α, ∫⁻ s in Set.Ioc (0 : ℝ) t,
            ENNReal.ofReal (R.Lb s.toNNReal ω' * (cnt pos 𝒜 N (G.Γα α) : ℝ) / S N α ^ 2) *
              ∑ i' ∈ nbr pos 𝒜 N (G.Γα α), ∫⁻ ω,
                (‖lft (XN i) s ω - lft (Xbar i) s ω‖ₑ ^ 2 +
                  lintegral R.lam (fun u => ‖lft (XN i') (s + u) ω - lft (Xbar i') (s + u) ω‖ₑ ^ 2 +
                    (Set.Iio (0 : ℝ)).indicator
                      (fun u => ‖XN i' (s + u) ω - Xbar i' (s + u) ω‖ₑ ^ 2) u)) ∂Pr := by sorry

end NeuroMV.Chaos
