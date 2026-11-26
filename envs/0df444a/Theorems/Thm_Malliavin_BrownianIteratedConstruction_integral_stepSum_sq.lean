-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_integral_stepSum_sq
-- name    : Malliavin.BrownianIteratedConstruction.integral_stepSum_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:28:15.856809+00:00
-- url     : https://prove2.me/theorems/78c6df6f-b252-4172-9850-036d34d5a4f0
-- title:
--   Brownian Iterated Construction: integral step Sum sq
-- statement:
--   The second moment of a finite Brownian step sum is the squared norm of its deterministic
--   step kernel.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianWickIsometry.lean#L48-L59
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianWickIsometry.lean#L48-L59

import Definitions.Def_Malliavin_GaussianHermite
import Definitions.Def_Malliavin_BrownianPolynomialHermite
import Definitions.Def_Malliavin_BrownianWickIsometry
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
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P]

theorem Malliavin.BrownianIteratedConstruction.integral_stepSum_sq (hB : IsPreBrownianReal B P) (v : ℝ≥0 →₀ ℝ) :
    (∫ w, stepSum B v w ^ 2 ∂P) = ‖stepToLp v‖ ^ 2 := by sorry
