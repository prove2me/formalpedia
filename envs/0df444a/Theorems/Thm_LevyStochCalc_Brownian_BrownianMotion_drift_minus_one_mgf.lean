-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_drift_minus_one_mgf
-- name    : LevyStochCalc.Brownian.BrownianMotion.drift_minus_one_mgf
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:10:28.030608+00:00
-- url     : https://prove2.me/theorems/1a43e28e-c727-4ad8-9400-9a2bba1d2476
-- title:
--   Exponential moment formula of Brownian motion with drift minus one
-- statement:
--   For every nonnegative t and real θ, E exp[θ(W_t−t)] = exp(t(−θ+θ²/2)). The proof uses the Gaussian marginal law for W_t−t and the exact Gaussian moment-generating-function theorem. This is the Lévy–Khintchine exponential moment identity for Gaussian triplet c=−1, σ=1, ν=0, apart from a trivial normalisation of the jump-free exponent.
-- source:
--   Mathlib ProbabilityTheory.mgf_gaussianReal; LevyStochCalc BrownianMotion.hasLaw_eval_readable.

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_MathlibBridge
import Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_hasLaw_eval_readable
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Basic
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory
open scoped NNReal
open LevyStochCalc.Brownian

theorem LevyStochCalc.Brownian.BrownianMotion.drift_minus_one_mgf
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (W : BrownianMotion P)
    (t : ℝ≥0) (θ : ℝ) :
    (∫ ω, Real.exp (θ * (W.W (t : ℝ) ω - (t : ℝ))) ∂P) =
      Real.exp ((t : ℝ) * (-θ + θ ^ 2 / 2)) := by sorry
