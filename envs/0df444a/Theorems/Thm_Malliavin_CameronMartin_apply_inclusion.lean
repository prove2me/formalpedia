-- Prove2me | Theorems.Thm_Malliavin_CameronMartin_apply_inclusion
-- name    : Malliavin.CameronMartin.apply_inclusion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:42:37.727775+00:00
-- url     : https://prove2.me/theorems/ffaf02dc-78c4-4610-b051-fd4f3d46ce60
-- title:
--   Cameron Martin: apply inclusion
-- statement:
--   Reproducing identity between the covariance embedding and the first-chaos inner product.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartin.lean#L223-L232
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartin.lean#L223-L232

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

theorem Malliavin.CameronMartin.apply_inclusion (L : StrongDual ℝ W) (h : Space μ) :
    L (inclusion μ h) = @inner ℝ _ _ (ofDual μ L) h := by sorry
