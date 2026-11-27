-- Prove2me | Theorems.Thm_GRH_positive_residue_of_logarithmic_derivative_at_a_zero
-- name    : GRH.positive_residue_of_logarithmic_derivative_at_a_zero
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-27T01:44:45.186866+00:00
-- url     : https://prove2.me/theorems/45104c90-1925-5b03-a30f-808127cb915f
-- title:
--   The logarithmic derivative of an entire function has positive integer residue at every zero
-- statement:
--   At a zero b of a nonzero entire function P, there is a positive integer m such that P is nonzero in a punctured neighborhood of b and (z−b)P′(z)/P(z) tends to m.
-- source:
--   Arithmetic reduction for GRH.centered_moebius_progression_bilinear_power_bound. The fixed-modulus equivalence is https://prove2.me/theorems/04e865ba-3dd7-43e6-9714-8e4d666e0b7c . Mathlib.Analysis.Analytic.Order and Mathlib.Analysis.Calculus.LogDeriv.

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.LogDeriv

open Filter Topology

theorem GRH.positive_residue_of_logarithmic_derivative_at_a_zero (P : ℂ → ℂ) (hP : Differentiable ℂ P) (hP0 : P ≠ 0)
    (b : ℂ) (hb : P b = 0) :
    ∃ m : ℕ, 0 < m ∧ (∀ᶠ z in 𝓝[≠] b, P z ≠ 0) ∧
      Tendsto (fun z => (z-b)*logDeriv P z) (𝓝[≠] b) (𝓝 (m:ℂ)) := by sorry
