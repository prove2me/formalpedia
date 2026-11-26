-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_integral_brownianPurePowerIntegral
-- name    : Malliavin.BrownianIteratedConstruction.integral_brownianPurePowerIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:25:54.275069+00:00
-- url     : https://prove2.me/theorems/01b68072-1446-531e-8d7c-681cf1908233
-- title:
--   Brownian Iterated Construction: integral brownian Pure Power Integral
-- statement:
--   Every positive-order Brownian pure-power multiple integral is centered.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerIntegral.lean#L60-L70
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerIntegral.lean#L60-L70

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

theorem Malliavin.BrownianIteratedConstruction.integral_brownianPurePowerIntegral
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {n : ℕ} (hn : 0 < n) (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    ∫ w, brownianPurePowerIntegral hB n f w ∂P = 0 := by sorry
