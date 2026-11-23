-- Prove2me | Theorems.Thm_Kyprianou_Ch02_finiteSimpleCharIntegrandDCTV1
-- name    : Kyprianou.Ch02.finiteSimpleCharIntegrandDCTV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T18:40:41.818818+00:00
-- url     : https://prove2.me/theorems/6a677f8e-2383-42b5-80e2-e77461ade7c3
-- title:
--   Finite-mark characteristic integral converges under pointwise simple approximants
-- statement:
--   Apply complex dominated convergence on finite measure ν.restrict B to exp(i ξ f_n(x))-1, whose norm is at most 2 from Complex.norm_exp_I_mul_ofReal and norm_sub_le. Use continuity of y↦exp(i ξ y)-1 and pointwise f_n(x)→x. This is a child of prmFiniteSimpleCharToRawKLSV1 and closes the analytic exponent-limit step.
-- source:
--   Kyprianou (2006) Chapter 2 Eq. (2.3).

import Mathlib
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.finiteSimpleCharIntegrandDCTV1
    (ν : Measure ℝ) [SigmaFinite ν]
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤)
    (f : ℕ → SimpleFunc ℝ ℝ)
    (hf : ∀ x : ℝ, Tendsto (fun n => f n x) atTop (𝓝 x))
    (ξ : ℝ) :
    Tendsto (fun n => ∫ x in B,
      (Complex.exp (Complex.I * (((ξ * f n x : ℝ) : ℂ))) - 1) ∂ν)
      atTop (𝓝 (∫ x in B,
      (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1) ∂ν)) := by sorry
