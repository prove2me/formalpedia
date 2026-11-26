-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_inner_brownianPurePowerIntegral
-- name    : Malliavin.BrownianIteratedConstruction.inner_brownianPurePowerIntegral
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:09:23.74571+00:00
-- url     : https://prove2.me/theorems/bc9f1f07-04b1-5559-8c90-b71b9fdd469e
-- title:
--   Brownian Iterated Construction: inner brownian Pure Power Integral
-- statement:
--   Factorial isometry for genuine Brownian multiple integrals of pure powers.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerIntegral.lean#L74-L83
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerIntegral.lean#L74-L83

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

theorem Malliavin.BrownianIteratedConstruction.inner_brownianPurePowerIntegral
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (n : ℕ) (f g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    inner ℝ (brownianPurePowerIntegral hB n f)
        (brownianPurePowerIntegral hB n g) =
      (n.factorial : ℝ) * inner ℝ f g ^ n := by sorry
