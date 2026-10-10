-- Prove2me | Theorems.Thm_NeuroMV_WellPosed_uniqueness
-- name    : NeuroMV.WellPosed.uniqueness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:46:50.366351+00:00
-- url     : https://prove2.me/theorems/8c045bfc-cb4c-4599-b9df-f54df9db678f
-- title:
--   §2, uniqueness, pp. 16–17 — two strong solutions of (6) in L∞–L² agree: sup_{s≤T} 𝔼∫_Γ|X^r_s − Y^r_s|² 𝓡(dr) = 0
-- statement:
--   Assume the model of (6) with Hypothesis 1.1 (H1)–(H5). Fix $\omega'$ and $T>0$, and let $X$ and $Y$ be two strong solutions of (6) on $[-\tau,T]$ at $\omega'$, both measurable in $(r,\omega)$ and in $L^\infty([-\tau,T],dt;L^2(\Omega\times\Gamma,\mathbb P\otimes\mathcal R;\mathbb R^d))$. Then
--
--   $$\sup_{s\le T}\,\mathbb E\int_\Gamma\big|X^r_s - Y^r_s\big|^2\,\mathcal R(dr) = 0,$$
--
--   i.e. $X_s = Y_s$ in $L^2(\Omega\times\Gamma,\mathbb P\otimes\mathcal R)$ for every $s\in[-\tau,T]$. This is the uniqueness half of Theorem 1.5 at a fixed $\omega'$.
--
--   **Formalization Note.** Stated for every $s\in[-\tau,T]$ as an iterated lower integral in $[0,\infty]$. (H6) is omitted (network only).
-- source:
--   Mehri, Scheutzow, Stannat, Zangeneh, Propagation of Chaos for Stochastic Spatially Structured Neuronal Networks with Delay driven by Jump Diffusions, arXiv:1805.01654v3, §2, proof of Theorem 1.5, Uniqueness, pp. 16–17 (last display of §2, p. 17)

import Mathlib
import Definitions.Def_NeuroMV_WellPosed_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace NeuroMV.WellPosed

open EthierKurtz

theorem uniqueness
    {d m n k P : ℕ} {U Ω Ω' : Type*} [MeasurableSpace U] [MeasurableSpace Ω] [MeasurableSpace Ω']
    (S : Space k P) (C : Coeffs d m n k U Ω') (hC : C.Regular)
    (ν : Measure U) [SigmaFinite ν] (τ : ℝ) (hτ : 0 < τ)
    (Nz : Noise d m n P U Ω) (hN : IsNoise τ ν Nz)
    (lam : Measure ℝ) (K L Kb Lb : ℝ≥0 → Ω' → ℝ) (Kt : ℝ → ℝ≥0 → Ω' → ℝ)
    (hH : Hyp1_1 S C ν τ lam K L Kb Lb Kt)
    (ω' : Ω') (T : ℝ) (hT : 0 < T) (X Y : Pos k → ℝ → Ω → SDEState d)
    (hX : IsStrongSol6 S C ν Nz τ ω' T X) (hXc : InClass S Nz.prob τ T X)
    (hY : IsStrongSol6 S C ν Nz τ ω' T Y) (hYc : InClass S Nz.prob τ T Y) :
    ∀ t ∈ Set.Icc (-τ) T, ∫⁻ r, ∫⁻ ω, ‖X r t ω - Y r t ω‖ₑ ^ 2 ∂Nz.prob ∂S.R = 0 := by sorry

end NeuroMV.WellPosed
