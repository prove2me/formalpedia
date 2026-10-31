-- Prove2me | Theorems.Thm_HighDimStat_Rkhs_mercer_spectral_basis_and_continuous_reps
-- name    : HighDimStat.Rkhs.mercer_spectral_basis_and_continuous_reps
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-31T04:05:42.530999+00:00
-- url     : https://prove2.me/theorems/9fad8a0b-909c-4d18-8fe8-a2482a9378b4
-- title:
--   Spectral basis and continuous eigenfunction representatives for Mercer kernel operator
-- statement:
--   For a continuous positive semidefinite kernel $K$ on a compact metric space $(X, P)$ with full-support finite Borel measure $P$, the Hilbert--Schmidt integral operator $T_K$ on $L^2(X; P)$ admits a countable Hilbert basis $(\varphi_j)_{j \in \iota}$ of eigenfunctions with non-negative eigenvalues $\mu_j \ge 0$, continuous representatives $\psi_j$ when $\mu_j > 0$, uniform convergence along every enumeration of $\iota$ by $\mathbb{N}$, and absolute pointwise convergence $\sum_j \mu_j \psi_j(x) \psi_j(z) = K(x, z)$.
-- source:
--   Wainwright, High-Dimensional Statistics (2019), Theorem 12.20, p. 395

import Mathlib
import Definitions.Def_HighDimStat_Rkhs_Core

open scoped RealInnerProductSpace
open MeasureTheory

namespace HighDimStat.Rkhs

theorem mercer_spectral_basis_and_continuous_reps {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (P : Measure X) [IsFiniteMeasure P] [P.IsOpenPosMeasure]
    (K : X → X → ℝ) (hKcont : Continuous (Function.uncurry K)) (hKpsd : IsPSDKernel K)
    (hHS : Integrable (fun p : X × X => (K p.1 p.2) ^ 2) (P.prod P))
    (TK : Lp ℝ 2 P →ₗ[ℝ] Lp ℝ 2 P)
    (hTK : ∀ f : Lp ℝ 2 P, (TK f : X → ℝ) =ᵐ[P] fun x => ∫ z, K x z * (f z) ∂P) :
    ∃ (ι : Type) (_ : Countable ι) (φ : HilbertBasis ι ℝ (Lp ℝ 2 P)) (μ : ι → ℝ)
      (ψ : ι → X → ℝ),
      (∀ j, 0 ≤ μ j) ∧
      (∀ j, TK (φ j) = μ j • (φ j : Lp ℝ 2 P)) ∧
      (∀ j, (φ j : X → ℝ) =ᵐ[P] ψ j) ∧
      (∀ j, 0 < μ j → Continuous (ψ j)) ∧
      (∀ e : ℕ ≃ ι, TendstoUniformly (fun n : ℕ => fun p : X × X =>
          ∑ k ∈ Finset.range n, μ (e k) * ψ (e k) p.1 * ψ (e k) p.2)
        (Function.uncurry K) Filter.atTop) ∧
      (∀ x z, HasSum (fun j => μ j * ψ j x * ψ j z) (K x z)) := by sorry

end HighDimStat.Rkhs
