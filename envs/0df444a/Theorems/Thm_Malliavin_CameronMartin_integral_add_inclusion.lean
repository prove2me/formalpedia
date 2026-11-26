-- Prove2me | Theorems.Thm_Malliavin_CameronMartin_integral_add_inclusion
-- name    : Malliavin.CameronMartin.integral_add_inclusion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:47:23.661633+00:00
-- url     : https://prove2.me/theorems/bbec05f9-1b88-4a1b-b65e-dcb4655e4896
-- title:
--   Cameron Martin: integral add inclusion
-- statement:
--   **The Cameron--Martin translation formula for Bochner integrals**: for a continuous `F` and a
--   Cameron--Martin vector `h`, `∫ F (x + inclusion μ h) dμ = ∫ F x · exp (h x - ‖h‖² / 2) dμ`.
--   Without an integrability hypothesis this remains a formal Bochner-integral identity; Lean defines
--   the integral to be zero in a nonintegrable case.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartinTheorem.lean#L576-L588
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartinTheorem.lean#L576-L588

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

theorem Malliavin.CameronMartin.integral_add_inclusion {F : W → ℝ} (hF : Continuous F) (h : Space μ) :
    ∫ x, F (x + inclusion μ h) ∂μ =
      ∫ x, F x * Real.exp ((h : Lp ℝ 2 μ) x - ‖h‖ ^ 2 / 2) ∂μ := by sorry
