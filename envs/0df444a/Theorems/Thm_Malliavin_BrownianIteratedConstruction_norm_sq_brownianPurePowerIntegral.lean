-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_norm_sq_brownianPurePowerIntegral
-- name    : Malliavin.BrownianIteratedConstruction.norm_sq_brownianPurePowerIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:10:21.391004+00:00
-- url     : https://prove2.me/theorems/42a5077c-6614-46e1-ac8b-cd81509f5748
-- title:
--   Brownian Iterated Construction: norm sq brownian Pure Power Integral
-- statement:
--   Squared norm of a genuine Brownian multiple integral of a pure power.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerIntegral.lean#L98-L104
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerIntegral.lean#L98-L104

import Definitions.Def_Malliavin_IteratedKernelPurePower
import Definitions.Def_Malliavin_BrownianPolynomialHermite
import Definitions.Def_Malliavin_BrownianPurePowerIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin Malliavin.BrownianIteratedConstruction
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [CompleteSpace W] [BorelSpace W]

theorem Malliavin.BrownianIteratedConstruction.norm_sq_brownianPurePowerIntegral
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (n : ℕ) (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    ‖brownianPurePowerIntegral hB n f‖ ^ 2 =
      (n.factorial : ℝ) * (‖f‖ ^ 2) ^ n := by sorry
