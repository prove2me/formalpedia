-- Prove2me | Theorems.Thm_Malliavin_CameronMartin_law_eq_centeredGaussian
-- name    : Malliavin.CameronMartin.law_eq_centeredGaussian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:43:48.218377+00:00
-- url     : https://prove2.me/theorems/bf983f81-8473-5232-8fa7-26d3964874ff
-- title:
--   Cameron Martin: law eq centered Gaussian
-- statement:
--   A centered Gaussian element of `L²(μ)` has law `N(0, ‖f‖²)`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartinTheorem.lean#L302-L309
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartinTheorem.lean#L302-L309

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

theorem Malliavin.CameronMartin.law_eq_centeredGaussian {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Lp ℝ 2 μ)
    (hfG : HasGaussianLaw (f : Ω → ℝ) μ) (hf₀ : ∫ x, f x ∂μ = 0) :
    μ.map (f : Ω → ℝ) = gaussianReal 0 (‖f‖₊ ^ 2) := by sorry
