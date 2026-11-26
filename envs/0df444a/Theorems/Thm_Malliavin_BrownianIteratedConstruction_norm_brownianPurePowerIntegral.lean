-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_norm_brownianPurePowerIntegral
-- name    : Malliavin.BrownianIteratedConstruction.norm_brownianPurePowerIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:27:17.702827+00:00
-- url     : https://prove2.me/theorems/d4535b0f-8af6-4734-932f-401b99e0c0b0
-- title:
--   Brownian Iterated Construction: norm brownian Pure Power Integral
-- statement:
--   Exact norm of a genuine Brownian multiple integral of a pure power.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerIntegral.lean#L108-L121
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerIntegral.lean#L108-L121

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

theorem Malliavin.BrownianIteratedConstruction.norm_brownianPurePowerIntegral
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (n : ℕ) (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    ‖brownianPurePowerIntegral hB n f‖ =
      Real.sqrt (n.factorial : ℝ) * ‖f‖ ^ n := by sorry
