-- Prove2me | Theorems.Thm_Kyprianou_Ch02_finiteDiracMarkIntegralTendstoV1
-- name    : Kyprianou.Ch02.finiteDiracMarkIntegralTendstoV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T13:58:24.300268+00:00
-- url     : https://prove2.me/theorems/6d80ef7b-5e4b-48b3-ab09-bdd98bc4bd8f
-- title:
--   Finite weighted Dirac measure signed mark integrals converge under pointwise approximations
-- statement:
--   For a finite sum of Dirac masses on real time-mark space with finite ENNReal coefficients, pointwise convergence of real mark functions f_n(x)→x entails convergence of their signed Bochner integrals to the integral of the mark. Express each integral as a finite sum using integral_finset_sum_measure, integral_smul_measure, integral_dirac, and prove finite-sum convergence with tendsto_finset_sum. Use integrable_smul_measure and integrable_dirac for each mass. This is the deterministic leaf needed by the Chapter 2 finite-window Poisson Dirac representation for Eq. (2.3).
-- source:
--   MeasureTheory finite atomic integration; Kyprianou (2006) Chapter 2 finite activity PRM.

import Mathlib
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.finiteDiracMarkIntegralTendstoV1
    (μ : Measure (ℝ × ℝ))
    (s : Finset (ℝ × ℝ)) (c : ℝ × ℝ → ℝ≥0∞)
    (hc : ∀ p ∈ s, c p ≠ ⊤)
    (hμ : μ = ∑ p ∈ s, c p • Measure.dirac p)
    (f : ℕ → ℝ → ℝ)
    (hf : ∀ x : ℝ, Tendsto (fun n => f n x) atTop (𝓝 x)) :
    Tendsto (fun n => ∫ z : ℝ × ℝ, f n z.2 ∂μ)
      atTop (𝓝 (∫ z : ℝ × ℝ, z.2 ∂μ)) := by sorry
