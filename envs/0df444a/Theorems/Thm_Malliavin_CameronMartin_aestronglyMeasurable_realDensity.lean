-- Prove2me | Theorems.Thm_Malliavin_CameronMartin_aestronglyMeasurable_realDensity
-- name    : Malliavin.CameronMartin.aestronglyMeasurable_realDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:54:46.287797+00:00
-- url     : https://prove2.me/theorems/7fea60fb-4b75-58b0-b7cc-d2e1abe5d093
-- title:
--   Cameron Martin: aestrongly Measurable real Density
-- statement:
--   The real-valued density is strongly measurable, hence also strongly measurable almost
--   everywhere for every reference measure on `W`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartinTheorem.lean#L92-L95
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartinTheorem.lean#L92-L95

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

theorem Malliavin.CameronMartin.aestronglyMeasurable_realDensity (h : Space μ) :
    AEStronglyMeasurable (realDensity μ h) μ := by sorry
