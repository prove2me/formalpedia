-- Prove2me | Theorems.Thm_Malliavin_CameronMartin_measurable_realDensity
-- name    : Malliavin.CameronMartin.measurable_realDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:43:39.871892+00:00
-- url     : https://prove2.me/theorems/a2ddf993-c704-54ed-be85-4f9fb6f3e97a
-- title:
--   Cameron Martin: measurable real Density
-- statement:
--   The real-valued Cameron--Martin density is measurable.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartinTheorem.lean#L86-L87
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartinTheorem.lean#L86-L87

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
omit [CompleteSpace W] [SecondCountableTopology W]

theorem Malliavin.CameronMartin.measurable_realDensity (h : Space μ) : Measurable (realDensity μ h) := by sorry
