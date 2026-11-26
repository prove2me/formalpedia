-- Prove2me | Theorems.Thm_Malliavin_CameronMartin_density_ne_top
-- name    : Malliavin.CameronMartin.density_ne_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:43:43.688021+00:00
-- url     : https://prove2.me/theorems/42296edc-328c-5987-a0fc-d0d429c14d3a
-- title:
--   Cameron Martin: density ne top
-- statement:
--   A Cameron--Martin density is finite everywhere.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartinTheorem.lean#L115-L116
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartinTheorem.lean#L115-L116

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

theorem Malliavin.CameronMartin.density_ne_top (h : Space μ) (x : W) : density μ h x ≠ ∞ := by sorry
