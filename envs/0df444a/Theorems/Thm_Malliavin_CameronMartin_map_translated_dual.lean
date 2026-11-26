-- Prove2me | Theorems.Thm_Malliavin_CameronMartin_map_translated_dual
-- name    : Malliavin.CameronMartin.map_translated_dual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:46:18.410993+00:00
-- url     : https://prove2.me/theorems/1693c09c-2b2e-593f-ac92-9c4b1bcac044
-- title:
--   Cameron Martin: map translated dual
-- statement:
--   The law of a continuous linear functional under the translated Gaussian measure: the
--   Gaussian with mean shifted by `L (inclusion μ h)` and unchanged variance `‖ofDual μ L‖²`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartinTheorem.lean#L452-L471
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartinTheorem.lean#L452-L471

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

theorem Malliavin.CameronMartin.map_translated_dual (h : Space μ) (L : StrongDual ℝ W) :
    (translated μ h).map L =
      gaussianReal (L (mean μ) + L (inclusion μ h)) (‖ofDual μ L‖₊ ^ 2) := by sorry
