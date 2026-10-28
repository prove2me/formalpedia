-- Prove2me | Theorems.Thm_ItoLemma_clock_augmented_coefficient_contraction
-- name    : ItoLemma.clock_augmented_coefficient_contraction
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:27:35.376005+00:00
-- url     : https://prove2.me/theorems/edd41311-329e-4f55-9efd-2da7d66fdf62
-- title:
--   Clock-Augmented Drift, Noise and Hessian Contractions
-- statement:
--   For a two-coordinate Itô process whose first coordinate is deterministic time and whose second coordinate has drift μ and Brownian diffusion σ, the gradient drift contraction equals the time derivative plus μ times the spatial derivative. Its diffusion contraction is σ times the spatial derivative. The quadratic-variation contraction of any Hessian equals σ² times its spatial-spatial entry. This is the finite-dimensional algebra needed when applying an existing time-independent vector Itô theorem to the clock-augmented state (t,Xₜ).
-- source:
--   Original algebraic bridge derived from the time-space embedding for Itô's lemma in https://en.wikipedia.org/wiki/It%C3%B4%27s_lemma (accessed 26 October 2026), to specialise Prove2Me's accepted vector Itô theorem UUID 550fc0f9-7957-4075-b3fb-68172654fce1. The assertion is finite-dimensional algebra, not the stochastic formula itself.

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic

open scoped BigOperators

/-- The clock has unit drift and zero Brownian diffusion; the spatial
coordinate has drift μ and diffusion σ. Contracting the vector Itô
coefficients therefore retains only the spatial Hessian term. -/

theorem ItoLemma.clock_augmented_coefficient_contraction
    (gradient : Fin 2 → ℝ) (hessian : Fin 2 → Fin 2 → ℝ) (μ σ : ℝ) :
    (∑ i : Fin 2, gradient i * (if i = 0 then (1 : ℝ) else μ)) =
      gradient 0 + gradient 1 * μ ∧
    (∑ i : Fin 2, gradient i * (if i = 0 then (0 : ℝ) else σ)) =
      gradient 1 * σ ∧
    (∑ i : Fin 2, ∑ j : Fin 2,
      hessian i j * (if i = 0 then (0 : ℝ) else σ) *
        (if j = 0 then (0 : ℝ) else σ)) =
      hessian 1 1 * σ ^ 2 := by sorry
