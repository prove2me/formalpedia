-- Prove2me | Theorems.Thm_Malliavin_CameronMartin_inner_ofDual
-- name    : Malliavin.CameronMartin.inner_ofDual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:54:39.305941+00:00
-- url     : https://prove2.me/theorems/336b242b-d40a-5bd9-81f4-1a03265a89f3
-- title:
--   Cameron Martin: inner of Dual
-- statement:
--   The `L²` inner product of generators is the covariance bilinear form.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartin.lean#L250-L261
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartin.lean#L250-L261

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

theorem Malliavin.CameronMartin.inner_ofDual (L K : StrongDual ℝ W) :
    @inner ℝ _ _ (ofDual μ L) (ofDual μ K) = covarianceBilinDual μ L K := by sorry
