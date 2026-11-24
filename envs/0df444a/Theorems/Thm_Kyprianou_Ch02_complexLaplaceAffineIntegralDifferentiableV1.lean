-- Prove2me | Theorems.Thm_Kyprianou_Ch02_complexLaplaceAffineIntegralDifferentiableV1
-- name    : Kyprianou.Ch02.complexLaplaceAffineIntegralDifferentiableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:58:41.463909+00:00
-- url     : https://prove2.me/theorems/e7c89b96-9ca3-48da-b2d2-89b0d81a47bd
-- title:
--   complexLaplaceAffineIntegralDifferentiable
-- statement:
--   complexLaplaceAffineIntegralDifferentiable
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.15

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.complexLaplaceAffineIntegralDifferentiableV1
    (μ : Measure ℝ) (hpos : ∀ᵐ x ∂μ, 0 ≤ x)
    (hint : Integrable (fun x : ℝ => min (1 : ℝ) |x|) μ)
    (a b : ℂ)
    (hi : ∀ z : ℂ, 0 < z.re →
      Integrable (fun x : ℝ => a + b * Complex.exp (-z * (x : ℂ))) μ) :
    DifferentiableOn ℂ (fun z : ℂ => ∫ x, a + b * Complex.exp (-z * (x : ℂ)) ∂μ)
      {z : ℂ | 0 < z.re} := by sorry
