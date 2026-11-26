-- Prove2me | Theorems.Thm_Malliavin_CameronMartin_density_toReal
-- name    : Malliavin.CameronMartin.density_toReal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:42:44.173683+00:00
-- url     : https://prove2.me/theorems/0255b06a-9ea2-5ff5-bf93-0488e660273a
-- title:
--   Cameron Martin: density to Real
-- statement:
--   Converting the extended nonnegative density back to `ℝ` recovers `realDensity`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartinTheorem.lean#L121-L123
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartinTheorem.lean#L121-L123

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

theorem Malliavin.CameronMartin.density_toReal (h : Space μ) (x : W) :
    (density μ h x).toReal = realDensity μ h x := by sorry
