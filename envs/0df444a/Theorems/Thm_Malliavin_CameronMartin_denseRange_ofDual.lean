-- Prove2me | Theorems.Thm_Malliavin_CameronMartin_denseRange_ofDual
-- name    : Malliavin.CameronMartin.denseRange_ofDual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:45:23.597104+00:00
-- url     : https://prove2.me/theorems/cb775813-3d75-5e6a-aa10-a49a3c2d5e0b
-- title:
--   Cameron Martin: dense Range of Dual
-- statement:
--   The range of `ofDual` is dense by construction.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartin.lean#L151-L164
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartin.lean#L151-L164

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
omit [CompleteSpace W] [SecondCountableTopology W]

theorem Malliavin.CameronMartin.denseRange_ofDual : DenseRange (ofDual μ) := by sorry
