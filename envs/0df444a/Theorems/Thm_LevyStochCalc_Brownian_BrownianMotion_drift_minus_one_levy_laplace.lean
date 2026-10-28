-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_drift_minus_one_levy_laplace
-- name    : LevyStochCalc.Brownian.BrownianMotion.drift_minus_one_levy_laplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:18:52.40599+00:00
-- url     : https://prove2.me/theorems/2b64f355-76e8-4132-87f7-59710bdff7dc
-- title:
--   Drifted Brownian motion satisfies the exact Lévy–Khintchine Laplace transform and exponential integrability
-- statement:
--   For every t≥0 and θ∈ℝ, the drifted Brownian exponential has finite expectation and its expectation is exp(t ψ(θ)) for the canonical Avram Lévy–Khintchine exponent with triplet c=−1, σ=1, ν=0. The Gaussian mgf is always strictly positive, and the Bochner integral convention (zero for nonintegrable functions) therefore also certifies integrability. This precisely discharges the Laplace field of the proposed Gaussian process adapter.
-- source:
--   Accepted drift-minus-one Brownian mgf and zero-jump Lévy exponent lemmas; Mathlib Integrable.of_integral_ne_zero.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_drift_minus_one_mgf
import Theorems.Thm_AvramDividend_Classical_laplaceExponent_zero_jump_measure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory
open scoped NNReal
open LevyStochCalc.Brownian

theorem LevyStochCalc.Brownian.BrownianMotion.drift_minus_one_levy_laplace
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (W : BrownianMotion P)
    (t : ℝ≥0) (θ : ℝ) :
    Integrable (fun ω => Real.exp (θ * (W.W (t : ℝ) ω - (t : ℝ)))) P ∧
    (∫ ω, Real.exp (θ * (W.W (t : ℝ) ω - (t : ℝ))) ∂P) =
      Real.exp ((t : ℝ) * AvramDividend.Classical.laplaceExponent
        (-1) 1 (0 : Measure ℝ) θ) := by sorry
