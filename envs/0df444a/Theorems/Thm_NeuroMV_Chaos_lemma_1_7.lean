-- Prove2me | Theorems.Thm_NeuroMV_Chaos_lemma_1_7
-- name    : NeuroMV.Chaos.lemma_1_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:44:42.658279+00:00
-- url     : https://prove2.me/theorems/99c00c22-aa83-41c4-bb35-cce2c5a4692d
-- title:
--   Lemma 1.7, p. 8 — under Hypothesis 1.6, 𝔼|X^r_t − X^{r̃}_t|² ≤ C₂(t, ω′)ε for r, r̃ in one cell Γ^{m,ε}_α
-- statement:
--   Assume Hypothesis 1.6. Let $X$ be a strong solution of the McKean–Vlasov equation (6) on $[-\tau,T]$ at the disorder $\omega'$, on a filtered probability space $(\tilde\Omega,\tilde{\mathbb P})$ carrying the noise of (6) and initial conditions $\hat z^\alpha\in L^2(\tilde\Omega;\mathrm{Càdlàg}([-\tau,0];\mathbb R^d))$, with $X$ in $L^\infty([-\tau,T];L^2(\tilde\Omega\times\Gamma,\tilde{\mathbb P}\otimes\mathcal R))$. Then for every $\varepsilon>0$, every $\alpha$ and every cell $\Gamma^{m,\varepsilon}_\alpha$ of the partition of Hypothesis 1.6,
--   $$\mathbb E\big|X^r_t-X^{\tilde r}_t\big|^2\le C_2(t,\omega')\,\varepsilon\qquad\text{for all } r,\tilde r\in\Gamma^{m,\varepsilon}_\alpha,\ t\in[-\tau,T],$$
--   where $C_2(t,\omega')=\exp\big[\int_0^t(L_s(\omega')+P\bar L_s(\omega')+P)\,ds\big]\,(1+3C_1(t,\omega'))$ and $C_1$ is the constant (7) of Lemma 1.4.
--
--   The lemma quantifies the spatial regularity of the mean-field solution: positions in one cell of the partition carry nearly the same law. It enters the proof of Theorem 1.8 through the bound on $I^\Theta_\alpha$.
--
--   **Formalization Note.** All quantities are in $[0,\infty]$. For $t\in[-\tau,0]$ both sides are trivial (the two positions lie in the same $\Gamma_\alpha$ and share the initial condition $\hat z^\alpha$).
-- source:
--   Mehri, Scheutzow, Stannat, Zangeneh, Propagation of Chaos for Stochastic Spatially Structured Neuronal Networks with Delay driven by Jump Diffusions, arXiv:1805.01654v3, Lemma 1.7, p. 8, with Hypothesis 1.6, pp. 7–8, and (7), p. 6

import Mathlib
import Definitions.Def_NeuroMV_Chaos_Network

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace NeuroMV.Chaos

/-- **Lemma 1.7** (p. 8). Under Hypothesis 1.6, let `X` be a strong solution of (6) on `[-τ, T]`
at the disorder `ω'` (on the space `(ΩX, 𝓕X, PrX)` with noise `WX, BX, NX` and initial
conditions `ẑ`), in `L^∞([-τ, T]; L²(ΩX × Γ, PrX ⊗ 𝓡))`. Then for every `ε > 0`, every cell
`Γ^{m,ε}_α` of the partition of Hypothesis 1.6, all `r, r̃ ∈ Γ^{m,ε}_α` and `t ∈ [-τ, T]`,
`𝔼|X^r_t − X^{r̃}_t|² ≤ C₂(t, ω') ε`, with
`C₂(t, ω') = exp[∫_0^t (L_s + P L̄_s + P) ds] (1 + 3 C₁(t, ω'))`. -/
theorem lemma_1_7
    {d m n k P : ℕ} {U Ω' ΩX : Type*} [MeasurableSpace U] [MeasurableSpace Ω']
    [MeasurableSpace ΩX]
    (G : Geometry k P) (ν : Measure U) [SigmaFinite ν] (Pr' : Measure Ω')
    [IsProbabilityMeasure Pr'] (C : Coeffs d m n k P U Ω') (R : Rates Ω')
    (pos : ℕ → NeuroMV.WellPosed.Pos k) (𝒜 : ℕ → Finset ℕ) (S : ℕ → Fin P → ℝ) (Q : Partitions k P)
    (PrX : Measure ΩX) (𝓕X : Filtration ℝ≥0 ‹MeasurableSpace ΩX›)
    (WX : ℝ≥0 → ΩX → EthierKurtz.SDEState m) (BX : Fin P → ℝ≥0 → ΩX → EthierKurtz.SDEState n)
    (NX : ΩX → Set (ℝ≥0 × (Option (Fin P) × U))) (zh : Fin P → ℝ → ΩX → EthierKurtz.SDEState d)
    (hG : G.Valid) (hH : Hyp16 G ν C R pos 𝒜 S Pr' Q)
    (hnoise : IsNoise6 PrX 𝓕X ν WX BX NX) (hzh : IsInit PrX 𝓕X G.τ zh)
    (ω' : Ω') (T : ℝ) (hT : 0 < T) (X : NeuroMV.WellPosed.Pos k → ℝ → ΩX → EthierKurtz.SDEState d)
    (hX : IsStrongSol6 G ν C PrX 𝓕X WX BX NX zh ω' T X) (hcl : InClass G PrX T X) :
    ∀ ε : ℝ, 0 < ε → ∀ (α : Fin P) (mm : Fin (Q.M ε α)), ∀ r ∈ Q.part ε α mm,
      ∀ rt ∈ Q.part ε α mm, ∀ t ∈ Set.Icc (-G.τ) T,
        ∫⁻ ω, ‖X r t ω - X rt t ω‖ₑ ^ 2 ∂PrX ≤ C2 G R PrX zh t ω' * ENNReal.ofReal ε := by sorry

end NeuroMV.Chaos
