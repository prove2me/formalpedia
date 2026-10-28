-- Prove2me | Theorems.Thm_MeasureTheory_integral_mixture
-- name    : MeasureTheory.integral_mixture
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T15:10:11.492984+00:00
-- url     : https://prove2.me/theorems/0f059440-4cf1-44a7-8563-86b73c147f8b
-- title:
--   The integral against a mixture is the weighted sum of the integrals
-- statement:
--   Let $Z$ be a measurable space, let $\pi$ and $\rho$ be measures on $Z$, let
--   $f\colon Z\to\mathbb R$ be integrable with respect to each of them, and let $a,b\ge 0$ be real.
--   Then $f$ integrates against the mixture $a\pi+b\rho$ to
--
--   $$
--   \int_Z f \,\mathrm d(a\pi+b\rho) \;=\; a\int_Z f\,\mathrm d\pi \;+\; b\int_Z f\,\mathrm d\rho .
--   $$
--
--   No normalization is assumed: $a+b$ need not be $1$, and $\pi$ and $\rho$ need not be probability
--   measures, only ones against which $f$ is integrable.
--
--   This is the computational half of a mixture argument, the companion to the fact that a convex
--   combination of probability measures is a probability measure. Having formed a mixture, a proof
--   almost always has to evaluate an expectation under it, and the step is additivity of the
--   integral in the measure plus homogeneity under a scalar — true but tedious to redo, because the
--   scalars are extended-nonnegative and the integrability side conditions have to be carried
--   through both summands. Five accepted proofs here each do that work separately.
--
--   **Formalization Note.** The scalars are coerced with `ENNReal.ofReal`, so the mixture reads
--   `ENNReal.ofReal a • π + ENNReal.ofReal b • ρ`. `hπ` and `hρ` are `Integrable f` for the two
--   measures separately; integrability against the mixture follows and is not assumed.
-- source:
--   Five distinct accepted submissions prove this inline, each for itself. Carved from https://prove2.me/submissions/60e9c3d5-1ac3-4ae3-839d-92bea8b0af50, lines 178-186.

import Mathlib

set_option autoImplicit false
open MeasureTheory

theorem MeasureTheory.integral_mixture {Z : Type*} [MeasurableSpace Z]
    (π ρ : Measure Z) (f : Z → ℝ) (hπ : Integrable f π) (hρ : Integrable f ρ)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫ z, f z ∂(ENNReal.ofReal a • π + ENNReal.ofReal b • ρ)) =
      a * (∫ z, f z ∂π) + b * (∫ z, f z ∂ρ) := by sorry
