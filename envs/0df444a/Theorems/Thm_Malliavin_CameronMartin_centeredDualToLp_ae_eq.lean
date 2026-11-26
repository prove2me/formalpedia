-- Prove2me | Theorems.Thm_Malliavin_CameronMartin_centeredDualToLp_ae_eq
-- name    : Malliavin.CameronMartin.centeredDualToLp_ae_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:42:21.401438+00:00
-- url     : https://prove2.me/theorems/eb3f590a-4974-5dcc-abbf-c2d664ae7b33
-- title:
--   Cameron Martin: centered Dual To Lp ae eq
-- statement:
--   Pointwise description of `centeredDualToLp`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartin.lean#L112-L129
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartin.lean#L112-L129

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

theorem Malliavin.CameronMartin.centeredDualToLp_ae_eq (L : StrongDual ℝ W) :
    ((centeredDualToLp μ L : Lp ℝ 2 μ) : W → ℝ) =ᵐ[μ]
      fun x ↦ L x - L (mean μ) := by sorry
