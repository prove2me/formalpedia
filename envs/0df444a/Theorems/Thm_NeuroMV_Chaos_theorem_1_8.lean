-- Prove2me | Theorems.Thm_NeuroMV_Chaos_theorem_1_8
-- name    : NeuroMV.Chaos.theorem_1_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:43:22.817471+00:00
-- url     : https://prove2.me/theorems/f046f7ad-7ca1-463e-af0e-a8d1e51388a0
-- title:
--   Theorem 1.8, p. 9 — the network (1) converges to the mean-field limit (5): lim_N 𝓔 sup_{t∈[−τ,T], r∈𝒜_N} 𝔼|X^{r,𝒜_N}_t − X̄^r_t|² = 0
-- statement:
--   Let the spatially structured neuronal network (1) and its McKean–Vlasov limit be as in the definitions module: neurons at positions $r\in\mathcal A_N\subset\Gamma$, subpopulations $\Gamma_\alpha$ with weights $1/\mathcal S_{\mathcal A_N,\alpha}$, independent Brownian and Poisson noises per neuron, and a random disorder $\omega'$ with expectation $\mathcal E$. Assume Hypothesis 1.6 and the **chaotic initial condition**: the initial conditions $z^r$, $r\in\Gamma_\alpha\cap\bigcup_N\mathcal A_N$, are independent copies of $\hat z^\alpha\in L^2(\Omega;\mathrm{Càdlàg}([-\tau,0];\mathbb R^d))$.
--
--   Fix $T>0$. Suppose that for $\mathbb P'$-almost every $\omega'$: $X^{\mathcal A_N}(\omega')$ is a strong solution of (1) on $[-\tau,T]$ for every $N$; $X(\omega')$ is a strong solution of the McKean–Vlasov equation (6) on $[-\tau,T]$ in $L^\infty([-\tau,T];L^2(\tilde\Omega\times\Gamma,\tilde{\mathbb P}\otimes\mathcal R))$; and for every neuron $r\in\bigcup_N\mathcal A_N$, $\bar X^r(\omega')$ is a strong solution of the mean-field equation (5), started from the same $z^r$ and driven by the same noises as neuron $r$ of the network, with the mean-field input computed from the law of $X(\omega')$. Then
--   $$\lim_{N\to\infty}\mathcal E\sup_{t\in[-\tau,T],\,r\in\mathcal A_N}\mathbb E\big|X^{r,\mathcal A_N}_t-\bar X^r_t\big|^2=0,$$
--   that is, the network converges to the mean-field process in $L^2(\Omega',L^\infty([0,T],L^2(\Omega,\mathbb P)))$.
--
--   This is the propagation-of-chaos result of the paper: in the limit of many neurons, each neuron evolves independently, driven by its own noise and by the averaged influence of the population described by the McKean–Vlasov equation.
--
--   **Formalization Note.** The theorem is stated for every family of solutions of (1), (5) and (6) rather than for "the" solutions, so it does not depend on Proposition 1.2 or Theorem 1.5. All expectations and suprema are in $[0,\infty]$. The mean-field input of (5) is an expectation over the probability space of the solution of (6) (the copy $\hat X$ enters only through its law). Hypothesis 1.6 includes (H6) and the corrected (H1′) (see the definitions module).
-- source:
--   Mehri, Scheutzow, Stannat, Zangeneh, Propagation of Chaos for Stochastic Spatially Structured Neuronal Networks with Delay driven by Jump Diffusions, arXiv:1805.01654v3, Theorem 1.8, p. 9, with (1), p. 2, (5)–(6), p. 5, Hypothesis 1.6, pp. 7–8, and the remark on p. 6

import Mathlib
import Definitions.Def_NeuroMV_Chaos_Network

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace NeuroMV.Chaos

/-- **Theorem 1.8** (p. 9). Under Hypothesis 1.6 and the chaotic initial condition assumption,
for every `T > 0`: if for `ℙ'`-a.e. `ω'` the processes `X^{𝒜_N}(ω')` solve the network equation
(1) on `[-τ, T]` for every `N`, `X(ω')` is a solution of (6) on `[-τ, T]` in
`L^∞([-τ, T]; L²(Ω̃ × Γ, ℙ̃ ⊗ 𝓡))`, and `X̄(ω')` solves the mean-field equation (5) for every
neuron of `⋃_N 𝒜_N` (same initial conditions and drivers as the network, mean-field input from
the law of `X`), then
`lim_{N → ∞} 𝓔 sup_{t ∈ [-τ, T], r ∈ 𝒜_N} 𝔼|X^{r,𝒜_N}_t − X̄^r_t|² = 0`. -/
theorem theorem_1_8
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
    Tendsto (fun N : ℕ => ∫⁻ ω', ⨆ t ∈ Set.Icc (-G.τ) T, ⨆ i ∈ 𝒜 N,
        ∫⁻ ω, ‖XN N ω' i t ω - Xbar ω' i t ω‖ₑ ^ 2 ∂Pr ∂Pr') atTop (𝓝 0) := by sorry

end NeuroMV.Chaos
