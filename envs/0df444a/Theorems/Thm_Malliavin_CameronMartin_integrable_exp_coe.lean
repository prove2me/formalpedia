-- Prove2me | Theorems.Thm_Malliavin_CameronMartin_integrable_exp_coe
-- name    : Malliavin.CameronMartin.integrable_exp_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:43:05.813546+00:00
-- url     : https://prove2.me/theorems/e5bde63e-d18a-51fb-b4dd-d1c98d1acee1
-- title:
--   Cameron Martin: integrable exp coe
-- statement:
--   The exponential of a first-chaos representative is integrable.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartinTheorem.lean#L401-L412
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartinTheorem.lean#L401-L412

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

theorem Malliavin.CameronMartin.integrable_exp_coe (h : Space μ) :
    Integrable (fun x ↦ Real.exp ((h : Lp ℝ 2 μ) x)) μ := by sorry
