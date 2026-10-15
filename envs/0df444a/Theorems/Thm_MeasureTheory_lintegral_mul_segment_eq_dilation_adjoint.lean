-- Prove2me | Theorems.Thm_MeasureTheory_lintegral_mul_segment_eq_dilation_adjoint
-- name    : MeasureTheory.lintegral_mul_segment_eq_dilation_adjoint
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-15T08:06:14.797846+00:00
-- url     : https://prove2.me/theorems/2cebf51c-ccab-4a37-ab25-3e2f42668e6f
-- title:
--   Adjoint identity for weighted segment averages under Haar measure
-- statement:
--   Let E be a finite-dimensional real normed space with a Borel sigma-finite additive Haar measure mu. For arbitrary measurable functions f,h from E to the extended nonnegative reals, the integral of h(z) times the segment average of f(t z) over 0 <= t <= 1 equals the integral of f(y) times the ray average of t^(-dim E) h(y/t) over 0 < t <= 1. No integrability or finiteness assumption on either function is required. This is the adjoint formula for averaging over dilations, obtained by Tonelli and the change of variables y=t z. It applies to arbitrary weights h and arbitrary finite-dimensional norms, independently of balls or Riesz kernels.
-- source:
--   Haar dilation change of variables and Tonelli: Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar, Measure.map_addHaar_smul, and Mathlib.MeasureTheory.Measure.Prod, lintegral_lintegral_swap. Applied to the radial averaging argument in Hunter, Notes on Partial Differential Equations (revised 6/18/2014), https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, printed pp. 68-69, equation (3.14). This general weighted identity is a derived change-of-variables interface, rather than a verbatim theorem in Hunter.

import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral

open MeasureTheory Set Metric
open scoped ENNReal
set_option autoImplicit false

theorem MeasureTheory.lintegral_mul_segment_eq_dilation_adjoint {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [SecondCountableTopology E] (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    [SFinite μ] (f h : E → ENNReal) (hf : Measurable f) (hh : Measurable h) :
    (∫⁻ z, h z * (∫⁻ t in Icc (0 : ℝ) 1, f (t • z)) ∂μ) =
      ∫⁻ y, f y * (∫⁻ t in Ioc (0 : ℝ) 1,
        ENNReal.ofReal ((t ^ Module.finrank ℝ E)⁻¹) * h (t⁻¹ • y)) ∂μ := by sorry
