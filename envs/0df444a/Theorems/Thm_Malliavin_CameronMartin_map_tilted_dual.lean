-- Prove2me | Theorems.Thm_Malliavin_CameronMartin_map_tilted_dual
-- name    : Malliavin.CameronMartin.map_tilted_dual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:46:34.397799+00:00
-- url     : https://prove2.me/theorems/05634c8b-c647-4d31-804c-cee64bce950d
-- title:
--   Cameron Martin: map tilted dual
-- statement:
--   The law of a continuous linear functional under the exponential tilt by a first-chaos
--   element.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartinTheorem.lean#L505-L512
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartinTheorem.lean#L505-L512

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

theorem Malliavin.CameronMartin.map_tilted_dual (h : Space μ) (L : StrongDual ℝ W) :
    (μ.tilted (fun x ↦ (h : Lp ℝ 2 μ) x)).map L =
      gaussianReal (L (mean μ) + @inner ℝ _ _ (ofDual μ L) h) (‖ofDual μ L‖₊ ^ 2) := by sorry
