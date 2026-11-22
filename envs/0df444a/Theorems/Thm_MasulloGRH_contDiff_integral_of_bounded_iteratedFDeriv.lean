-- Prove2me | Theorems.Thm_MasulloGRH_contDiff_integral_of_bounded_iteratedFDeriv
-- name    : MasulloGRH.contDiff_integral_of_bounded_iteratedFDeriv
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T16:57:47.131917+00:00
-- url     : https://prove2.me/theorems/b4fcf340-9131-4030-9f6c-d9db6f56eef9
-- title:
--   Differentiation under the integral sign to all orders over a finite measure with uniformly bounded derivatives
-- statement:
--   Let $(Q,\mu)$ be a finite measure space, $V$ a real normed space, and $F:Q\times V\to\mathbb C$ such that each $F(q,\cdot)$ is $C^\infty$, each iterated derivative $q\mapsto D^k_yF(q,y)$ is (a.e.-strongly) measurable, and for every $k$ the $k$-th derivatives are bounded uniformly: $\sup_{q,y}\|D^k_yF(q,y)\|\le C_k<\infty$. Then $G(y)=\int_Q F(q,y)\,d\mu(q)$ is $C^\infty$ and one may differentiate under the integral sign to all orders:
--   $$D^kG(y)=\int_Q D^k_yF(q,y)\,d\mu(q)\qquad(k\ge0,\ y\in V).$$
--   Proof: induction on $k$ using dominated differentiation (the bound $C_{k+1}$ is integrable because $\mu$ is finite) and commuting the currying isometries with the Bochner integral.
--
--   In Masullo's Appendix D this is the analytic step showing that averaging a Schwartz–Bruhat function over a compact subgroup (with normalized Haar measure) preserves smoothness and controls every seminorm by the corresponding seminorm of the integrand.
-- source:
--   Standard (dominated differentiation under the integral sign, e.g. Dieudonné, Foundations of Modern Analysis 8.11); used in A. M. Masullo, The Music of the Primes, draft of 20 November 2026, Appendix D (averaging Schwartz–Bruhat functions over compact subgroups)

import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Basic

set_option autoImplicit false

namespace MasulloGRH

open MeasureTheory

theorem contDiff_integral_of_bounded_iteratedFDeriv
    {Q : Type*} [MeasurableSpace Q] (μ : Measure Q) [IsFiniteMeasure μ]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : Q → V → ℂ) (hF : ∀ q, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (F q))
    (hmeas : ∀ (k : ℕ) (y : V), AEStronglyMeasurable (fun q => iteratedFDeriv ℝ k (F q) y) μ)
    (hbd : ∀ k : ℕ, ∃ C : ℝ, ∀ q y, ‖iteratedFDeriv ℝ k (F q) y‖ ≤ C) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => ∫ q, F q y ∂μ) ∧
      ∀ (k : ℕ) (y : V), iteratedFDeriv ℝ k (fun y => ∫ q, F q y ∂μ) y =
        ∫ q, iteratedFDeriv ℝ k (F q) y ∂μ := by
  sorry

end MasulloGRH
