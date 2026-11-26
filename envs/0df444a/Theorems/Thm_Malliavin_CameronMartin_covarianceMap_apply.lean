-- Prove2me | Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
-- name    : Malliavin.CameronMartin.covarianceMap_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:42:21.671637+00:00
-- url     : https://prove2.me/theorems/e611d734-9b6c-4648-9ff7-ca93b734769a
-- title:
--   Cameron Martin: covariance Map apply
-- statement:
--   The Cameron Martin construction uses the covariance Map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartin.lean#L203-L211
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartin.lean#L203-L211

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

theorem Malliavin.CameronMartin.covarianceMap_apply (f : Lp ℝ 2 μ) :
    covarianceMap μ f = ∫ x, f x • centeredId μ x ∂μ := by sorry
