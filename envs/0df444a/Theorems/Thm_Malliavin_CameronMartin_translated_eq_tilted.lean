-- Prove2me | Theorems.Thm_Malliavin_CameronMartin_translated_eq_tilted
-- name    : Malliavin.CameronMartin.translated_eq_tilted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:46:28.7535+00:00
-- url     : https://prove2.me/theorems/472c8930-e306-4704-9a92-0733e795b8c8
-- title:
--   Cameron Martin: translated eq tilted
-- statement:
--   The analytic core of the Cameron--Martin theorem: translating by the covariance image of `h`
--   is the same as exponentially tilting by its first-chaos representative.  Both measures give
--   every continuous linear functional `L` the Gaussian law with mean `L (mean μ) + ⟪ofDual μ L, h⟫`
--   and variance `‖ofDual μ L‖²`, so they agree by `Measure.ext_of_charFunDual`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartinTheorem.lean#L518-L526
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartinTheorem.lean#L518-L526

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

theorem Malliavin.CameronMartin.translated_eq_tilted (h : Space μ) :
    translated μ h = μ.tilted (fun x ↦ (h : Lp ℝ 2 μ) x) := by sorry
