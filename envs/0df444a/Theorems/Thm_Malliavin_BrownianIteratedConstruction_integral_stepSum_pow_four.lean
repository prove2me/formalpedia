-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_integral_stepSum_pow_four
-- name    : Malliavin.BrownianIteratedConstruction.integral_stepSum_pow_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:28:27.217693+00:00
-- url     : https://prove2.me/theorems/e08b4faa-a66d-43f0-b18c-755ee8bceae8
-- title:
--   Brownian Iterated Construction: integral step Sum pow four
-- statement:
--   The fourth moment of a finite Brownian step sum is three times the squared variance.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianWickIsometry.lean#L64-L75
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianWickIsometry.lean#L64-L75

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

theorem Malliavin.BrownianIteratedConstruction.integral_stepSum_pow_four (hB : IsPreBrownianReal B P) (v : ℝ≥0 →₀ ℝ) :
    (∫ w, stepSum B v w ^ 4 ∂P) = 3 * (‖stepToLp v‖ ^ 2) ^ 2 := by sorry
