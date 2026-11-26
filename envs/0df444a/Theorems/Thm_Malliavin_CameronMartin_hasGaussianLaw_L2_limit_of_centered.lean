-- Prove2me | Theorems.Thm_Malliavin_CameronMartin_hasGaussianLaw_L2_limit_of_centered
-- name    : Malliavin.CameronMartin.hasGaussianLaw_L2_limit_of_centered
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:46:02.015425+00:00
-- url     : https://prove2.me/theorems/2e7a4195-bde1-5631-ac64-5e0e6f4ada4a
-- title:
--   Cameron Martin: has Gaussian Law L2 limit of centered
-- statement:
--   A limit in `L²` of centered Gaussian random variables is Gaussian.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartinTheorem.lean#L312-L339
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartinTheorem.lean#L312-L339

import Definitions.Def_Malliavin_CameronMartin
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Definitions.Def_Malliavin_CameronMartinTheorem
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Real Topology
noncomputable section
universe u v u_1 u_2 u_3 u_4 u_5 u_6 u_8
open Malliavin Malliavin.CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]

theorem Malliavin.CameronMartin.hasGaussianLaw_L2_limit_of_centered
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f : ℕ → Lp ℝ 2 μ} {g : Lp ℝ 2 μ} (hfg : Tendsto f atTop (𝓝 g))
    (hfG : ∀ n, HasGaussianLaw (f n : Ω → ℝ) μ)
    (hf₀ : ∀ n, ∫ x, f n x ∂μ = 0) : HasGaussianLaw (g : Ω → ℝ) μ := by sorry
