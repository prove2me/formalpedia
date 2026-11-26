-- Prove2me | Theorems.Thm_Malliavin_CameronMartin_mem_subspace_iff
-- name    : Malliavin.CameronMartin.mem_subspace_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:54:38.275569+00:00
-- url     : https://prove2.me/theorems/e0f61031-4453-4e06-8673-6acef99612c8
-- title:
--   Cameron Martin: mem subspace iff
-- statement:
--   The Cameron Martin construction uses the mem subspace iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartin.lean#L245-L247
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartin.lean#L245-L247

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

theorem Malliavin.CameronMartin.mem_subspace_iff (h : W) :
    h ∈ subspace μ ↔ ∃ k : Space μ, inclusion μ k = h := by sorry
