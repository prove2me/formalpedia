-- Prove2me | Theorems.Thm_Malliavin_CameronMartin_density_mul_neg_ae
-- name    : Malliavin.CameronMartin.density_mul_neg_ae
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:45:53.707012+00:00
-- url     : https://prove2.me/theorems/ed0f38d1-262d-4413-abc8-b337b661b925
-- title:
--   Cameron Martin: density mul neg ae
-- statement:
--   The product of the extended densities at opposite shifts is constant almost everywhere.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartinTheorem.lean#L170-L175
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartinTheorem.lean#L170-L175

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
omit [CompleteSpace W] [SecondCountableTopology W]

theorem Malliavin.CameronMartin.density_mul_neg_ae (h : Space μ) :
    (fun x ↦ density μ h x * density μ (-h) x) =ᵐ[μ]
      fun _ ↦ ENNReal.ofReal (Real.exp (-‖h‖ ^ 2)) := by sorry
