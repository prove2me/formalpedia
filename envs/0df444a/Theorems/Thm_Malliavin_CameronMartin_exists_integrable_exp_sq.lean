-- Prove2me | Theorems.Thm_Malliavin_CameronMartin_exists_integrable_exp_sq
-- name    : Malliavin.CameronMartin.exists_integrable_exp_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:54:43.338208+00:00
-- url     : https://prove2.me/theorems/bb4e3f1c-4e6f-4476-99c6-d8d6b5538018
-- title:
--   Cameron Martin: exists integrable exp sq
-- statement:
--   Fernique's exponential integrability, recorded at the Cameron--Martin interface.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartin.lean#L264-L269
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartin.lean#L264-L269

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

theorem Malliavin.CameronMartin.exists_integrable_exp_sq :
    ∃ C : ℝ, 0 < C ∧ Integrable (fun x ↦ Real.exp (C * ‖x‖ ^ 2)) μ := by sorry
