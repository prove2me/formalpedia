-- Prove2me | Theorems.Thm_NeuroMV_WellPosed_lemma_1_4
-- name    : NeuroMV.WellPosed.lemma_1_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:46:29.786003+00:00
-- url     : https://prove2.me/theorems/8fa94b30-b5db-4d49-82e0-71d15627f0c5
-- title:
--   Lemma 1.4, p. 6 — every measurable strong solution of (6) in L∞–L² has sup_{s∈[−τ,t]} 𝔼|X^r_s|² ≤ C₁(t, ω′)
-- statement:
--   Assume the model of (6) with Hypothesis 1.1 (H1)–(H5). Fix $\omega'$ and $T > 0$, and let $X$ be a strong solution of (6) on $[-\tau,T]$ at $\omega'$, measurable in $(r,\omega)$, that belongs to $L^\infty([-\tau,T],dt;L^2(\Omega\times\Gamma,\mathbb P\otimes\mathcal R;\mathbb R^d))$. Then
--
--   $$\sup_{s\in[-\tau,t]}\mathbb E\big[|X^r_s|^2\big] \le C_1(t,\omega'),\qquad r\in\Gamma,\ 0\le t\le T,$$
--
--   where
--
--   $$C_1(t,\omega') := \Big(\sup_{u\in[-\tau,0],\,1\le\zeta\le P}\mathbb E\big|\hat z^\zeta(u)\big|^2 + 1\Big)\exp\Big(\int_0^t\big(K_s(\omega') + 3P\bar K_s(\omega') + P\big)ds\Big). \tag{7}$$
--
--   The bound depends only on the initial data and the growth rates $K, \bar K$ of (H2), (H5); it is used in the uniqueness argument and, through (12), in the existence proof.
--
--   **Formalization Note.** The paper writes $t \le T$; the statement is for $t\in[0,T]$, the range on which $\int_0^t$ in (7) is meant. The paper's "for $\mathbb P'$-almost all $\omega'$" is the per-$\omega'$ statement applied to those $\omega'$. Expectations and suprema are in $[0,\infty]$. (H6) is omitted (network only).
-- source:
--   Mehri, Scheutzow, Stannat, Zangeneh, Propagation of Chaos for Stochastic Spatially Structured Neuronal Networks with Delay driven by Jump Diffusions, arXiv:1805.01654v3, Lemma 1.4 and (7), p. 6

import Mathlib
import Definitions.Def_NeuroMV_WellPosed_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace NeuroMV.WellPosed

open EthierKurtz

theorem lemma_1_4
    {d m n k P : ℕ} {U Ω Ω' : Type*} [MeasurableSpace U] [MeasurableSpace Ω] [MeasurableSpace Ω']
    (S : Space k P) (C : Coeffs d m n k U Ω') (hC : C.Regular)
    (ν : Measure U) [SigmaFinite ν] (τ : ℝ) (hτ : 0 < τ)
    (Nz : Noise d m n P U Ω) (hN : IsNoise τ ν Nz)
    (lam : Measure ℝ) (K L Kb Lb : ℝ≥0 → Ω' → ℝ) (Kt : ℝ → ℝ≥0 → Ω' → ℝ)
    (hH : Hyp1_1 S C ν τ lam K L Kb Lb Kt)
    (ω' : Ω') (T : ℝ) (hT : 0 < T) (X : Pos k → ℝ → Ω → SDEState d)
    (hX : IsStrongSol6 S C ν Nz τ ω' T X) (hXc : InClass S Nz.prob τ T X) :
    ∀ r ∈ S.Γ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ⨆ s ∈ Set.Icc (-τ) t, ∫⁻ ω, ‖X r s ω‖ₑ ^ 2 ∂Nz.prob ≤ C1 Nz τ K Kb t ω' := by sorry

end NeuroMV.WellPosed
