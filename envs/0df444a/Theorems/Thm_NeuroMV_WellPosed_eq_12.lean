-- Prove2me | Theorems.Thm_NeuroMV_WellPosed_eq_12
-- name    : NeuroMV.WellPosed.eq_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:47:50.213718+00:00
-- url     : https://prove2.me/theorems/39c6d74b-4f42-4a64-9d36-a948acb43758
-- title:
--   (12), p. 9 — the Euler scheme satisfies sup_{t∈[−τ,T]} 𝔼|X^{n,r}_t|² ≤ C₁(T, ω′) for all n and r
-- statement:
--   Assume the model of (6) with Hypothesis 1.1 (H1)–(H5). Fix $\omega'$, $T>0$ and $n \ge 1$, and let $X^{n}$ be a solution on $[-\tau,T]$ of the Euler scheme (11)/(13) at $\omega'$. Then for every $r\in\Gamma$,
--
--   $$\sup_{t\in[-\tau,T]}\mathbb E\big|X^{n,r}_t\big|^2 \le C_1(T,\omega'), \tag{12}$$
--
--   with $C_1(T,\omega') = \big(\sup_{u\in[-\tau,0],1\le\zeta\le P}\mathbb E|\hat z^\zeta(u)|^2 + 1\big)\exp\big(\int_0^T (K_s(\omega') + 3P\bar K_s(\omega') + P)ds\big)$ from (7). The bound is uniform in $n$ and $r$; it feeds the a priori estimates (ii)–(iii) and the convergence proof.
--
--   **Formalization Note.** Expectations and the supremum are in $[0,\infty]$. (H6) is omitted (network only).
-- source:
--   Mehri, Scheutzow, Stannat, Zangeneh, Propagation of Chaos for Stochastic Spatially Structured Neuronal Networks with Delay driven by Jump Diffusions, arXiv:1805.01654v3, §2, proof of Theorem 1.5, (12), p. 9; C₁ from (7), p. 6

import Mathlib
import Definitions.Def_NeuroMV_WellPosed_Scheme

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace NeuroMV.WellPosed

open EthierKurtz

theorem eq_12
    {d m n k P : ℕ} {U Ω Ω' : Type*} [MeasurableSpace U] [MeasurableSpace Ω] [MeasurableSpace Ω']
    (S : Space k P) (C : Coeffs d m n k U Ω') (hC : C.Regular)
    (ν : Measure U) [SigmaFinite ν] (τ : ℝ) (hτ : 0 < τ)
    (Nz : Noise d m n P U Ω) (hN : IsNoise τ ν Nz)
    (lam : Measure ℝ) (K L Kb Lb : ℝ≥0 → Ω' → ℝ) (Kt : ℝ → ℝ≥0 → Ω' → ℝ)
    (hH : Hyp1_1 S C ν τ lam K L Kb Lb Kt)
    (ω' : Ω') (T : ℝ) (hT : 0 < T) (ns : ℕ) (hns : 0 < ns) (Xn : Pos k → ℝ → Ω → SDEState d)
    (hX : IsEulerScheme6 S C ν Nz τ ω' T ns Xn) :
    ∀ r ∈ S.Γ, ⨆ t ∈ Set.Icc (-τ) T, ∫⁻ ω, ‖Xn r t ω‖ₑ ^ 2 ∂Nz.prob ≤ C1 Nz τ K Kb T ω' := by sorry

end NeuroMV.WellPosed
