-- Prove2me | Theorems.Thm_Malliavin_CameronMartin_measurable_density
-- name    : Malliavin.CameronMartin.measurable_density
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:43:27.227125+00:00
-- url     : https://prove2.me/theorems/580e4ffa-4546-4bc9-ab35-94aec18e0a11
-- title:
--   Cameron Martin: measurable density
-- statement:
--   The Cameron--Martin density is measurable.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartinTheorem.lean#L99-L100
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartinTheorem.lean#L99-L100

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

theorem Malliavin.CameronMartin.measurable_density (h : Space μ) : Measurable (density μ h) := by sorry
