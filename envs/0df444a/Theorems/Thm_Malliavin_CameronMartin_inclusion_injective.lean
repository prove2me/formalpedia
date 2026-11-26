-- Prove2me | Theorems.Thm_Malliavin_CameronMartin_inclusion_injective
-- name    : Malliavin.CameronMartin.inclusion_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:54:33.87979+00:00
-- url     : https://prove2.me/theorems/187a4143-847c-45d9-9734-a4fe403b779e
-- title:
--   Cameron Martin: inclusion injective
-- statement:
--   The covariance embedding is injective on the closed first chaos.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartin.lean#L235-L239
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartin.lean#L235-L239

import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Moments.CovarianceBilinDual
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_CameronMartin
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real Topology
universe u v u_1 u_2 u_3 u_4 u_5 u_6 u_7
open Malliavin
open Malliavin.CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]

theorem Malliavin.CameronMartin.inclusion_injective : Function.Injective (inclusion μ) := by sorry
