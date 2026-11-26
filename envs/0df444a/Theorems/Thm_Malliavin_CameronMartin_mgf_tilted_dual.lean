-- Prove2me | Theorems.Thm_Malliavin_CameronMartin_mgf_tilted_dual
-- name    : Malliavin.CameronMartin.mgf_tilted_dual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:46:22.561984+00:00
-- url     : https://prove2.me/theorems/82c1ea1f-0470-59ab-b599-1468d9201d2f
-- title:
--   Cameron Martin: mgf tilted dual
-- statement:
--   The moment generating function of a continuous linear functional under the exponential
--   tilt by a first-chaos element: Gaussian with mean `L (mean μ) + ⟪ofDual μ L, h⟫` and variance
--   `‖ofDual μ L‖²`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartinTheorem.lean#L476-L501
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartinTheorem.lean#L476-L501

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

theorem Malliavin.CameronMartin.mgf_tilted_dual (h : Space μ) (L : StrongDual ℝ W) (t : ℝ) :
    mgf L (μ.tilted (fun x ↦ (h : Lp ℝ 2 μ) x)) t =
      Real.exp ((L (mean μ) + @inner ℝ _ _ (ofDual μ L) h) * t +
        ((‖ofDual μ L‖₊ ^ 2 : ℝ≥0) : ℝ) * t ^ 2 / 2) := by sorry
