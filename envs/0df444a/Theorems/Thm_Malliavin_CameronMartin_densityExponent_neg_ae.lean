-- Prove2me | Theorems.Thm_Malliavin_CameronMartin_densityExponent_neg_ae
-- name    : Malliavin.CameronMartin.densityExponent_neg_ae
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:45:50.53173+00:00
-- url     : https://prove2.me/theorems/278a18d4-137f-40e3-b9d3-8509c8a5d647
-- title:
--   Cameron Martin: density Exponent neg ae
-- statement:
--   The density exponent at the negative Cameron--Martin vector, almost everywhere.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartinTheorem.lean#L147-L154
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartinTheorem.lean#L147-L154

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

theorem Malliavin.CameronMartin.densityExponent_neg_ae (h : Space μ) :
    densityExponent μ (-h) =ᵐ[μ]
      fun x ↦ -(h : Lp ℝ 2 μ) x - ‖h‖ ^ 2 / 2 := by sorry
