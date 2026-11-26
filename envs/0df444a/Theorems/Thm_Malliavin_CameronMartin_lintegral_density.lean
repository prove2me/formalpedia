-- Prove2me | Theorems.Thm_Malliavin_CameronMartin_lintegral_density
-- name    : Malliavin.CameronMartin.lintegral_density
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T10:54:57.748654+00:00
-- url     : https://prove2.me/theorems/cc041e28-0e3d-5f76-a01e-931127177fb7
-- title:
--   Cameron Martin: lintegral density
-- statement:
--   The Cameron--Martin density integrates to one.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartinTheorem.lean#L432-L437
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartinTheorem.lean#L432-L437

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

theorem Malliavin.CameronMartin.lintegral_density (h : Space μ) : ∫⁻ x, density μ h x ∂μ = 1 := by sorry
