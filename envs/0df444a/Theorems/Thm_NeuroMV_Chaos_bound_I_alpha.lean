-- Prove2me | Theorems.Thm_NeuroMV_Chaos_bound_I_alpha
-- name    : NeuroMV.Chaos.bound_I_alpha
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:43:15.196111+00:00
-- url     : https://prove2.me/theorems/7ffeb197-cca4-47d6-af54-19f98d82a18b
-- title:
--   §3, p. 20 — I^θ_α, I^β_α, I^η_α ≤ 6(#𝒜_N∩Γ_α/𝒮² + ε(#𝒜_N∩Γ_α)²/𝒮² + M^{(ε)}_α Σ_m(#𝒜_N∩Γ^{m,ε}_α/𝒮 − 𝓡(Γ^{m,ε}_α))²) C₂(t, ω′)
-- statement:
--   Assume Hypothesis 1.6 and the chaotic initial condition. Fix a disorder $\omega'$ at which $\hat X$ solves (6) in $L^\infty([-\tau,T];L^2)$ and $\bar X$ solves the mean-field equation (5) for every neuron of $\bigcup_N\mathcal A_N$. Then for every $N$, every neuron $r\in\mathcal A_N$, every $\alpha$, every $\varepsilon>0$ with its partition $\{\Gamma^{m,\varepsilon}_\alpha\}$ and every $t\in[0,T]$, each of $I^\theta_\alpha$, $I^\beta_\alpha$, $I^\eta_\alpha$ is at most
--   $$6\Big(\frac{\#\mathcal A_N\cap\Gamma_\alpha}{\mathcal S^2_{\mathcal A_N,\alpha}}+\varepsilon\frac{(\#\mathcal A_N\cap\Gamma_\alpha)^2}{\mathcal S^2_{\mathcal A_N,\alpha}}+M^{(\varepsilon)}_\alpha\sum_{m}\Big(\frac{\#(\mathcal A_N\cap\Gamma^{m,\varepsilon}_\alpha)}{\mathcal S_{\mathcal A_N,\alpha}}-\mathcal R(\Gamma^{m,\varepsilon}_\alpha)\Big)^2\Big)C_2(t,\omega').$$
--
--   The three summands are the three sources of error between the network and the mean field: the fluctuation of an empirical average of independent terms (where the chaotic initial condition enters), the spatial discretization within a cell (Lemma 1.7), and the mismatch between the neuron counts and the measure $\mathcal R$ (condition (10)).
--
--   **Formalization Note.** All quantities are in $[0,\infty]$. The page states the bound for $\Theta\in\{\theta,\beta\}$ and then "similar arguments imply" the same for $I^\eta_\alpha$; the three bounds are stated together. $I^\eta_\alpha$ carries the expectation $\mathbb E$ of (17), which the display on p. 20 omits.
-- source:
--   Mehri, Scheutzow, Stannat, Zangeneh, Propagation of Chaos for Stochastic Spatially Structured Neuronal Networks with Delay driven by Jump Diffusions, arXiv:1805.01654v3, §3, proof of Theorem 1.8, p. 20, the bounds on I^Θ_α and I^η_α

import Mathlib
import Definitions.Def_NeuroMV_Chaos_Network

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace NeuroMV.Chaos

/-- **The bound on `I^Θ_α`** (§3, p. 20). Under Hypothesis 1.6 and the chaotic initial condition,
at a disorder `ω'` where `X` solves (6) in `L^∞([-τ, T]; L²)` and `X̄` solves (5) for every
neuron of `⋃_N 𝒜_N`: for every `N`, every neuron `r = pos i` of `𝒜_N`, every `α`, every `ε > 0`
(with the partition of Hypothesis 1.6) and every `t ∈ [0, T]`, each of `I^θ_α`, `I^β_α`, `I^η_α`
is at most
`6 (#𝒜_N ∩ Γ_α / 𝒮²_{𝒜_N,α} + ε (#𝒜_N ∩ Γ_α)² / 𝒮²_{𝒜_N,α}
  + M^{(ε)}_α Σ_m (#(𝒜_N ∩ Γ^{m,ε}_α) / 𝒮_{𝒜_N,α} − 𝓡(Γ^{m,ε}_α))²) C₂(t, ω')`. -/
theorem bound_I_alpha
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
    (hXbar : ∀ i : ℕ, (∃ N, i ∈ 𝒜 N) → IsLimitSol G ν C pos Pr 𝓕 W B Nall z PrX X ω' T i (Xbar i)) :
    ∀ N : ℕ, ∀ i ∈ 𝒜 N, ∀ α : Fin P, ∀ ε : ℝ, 0 < ε → ∀ t ∈ Set.Icc (0 : ℝ) T,
      Iθ G C pos 𝒜 S Pr Xbar PrX X ω' N α i t ≤
          ENNReal.ofReal (6 * bracket G pos 𝒜 S Q N ε α) * C2 G R PrX zh t ω' ∧
        Iβ G C pos 𝒜 S Pr Xbar PrX X ω' N α i t ≤
          ENNReal.ofReal (6 * bracket G pos 𝒜 S Q N ε α) * C2 G R PrX zh t ω' ∧
        Iη G ν C pos 𝒜 S Pr Xbar PrX X ω' N α i t ≤
          ENNReal.ofReal (6 * bracket G pos 𝒜 S Q N ε α) * C2 G R PrX zh t ω' := by sorry

end NeuroMV.Chaos
