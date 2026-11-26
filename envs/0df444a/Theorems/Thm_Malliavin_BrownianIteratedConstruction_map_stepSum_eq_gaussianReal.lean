-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_map_stepSum_eq_gaussianReal
-- name    : Malliavin.BrownianIteratedConstruction.map_stepSum_eq_gaussianReal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:06:04.622537+00:00
-- url     : https://prove2.me/theorems/878fec2e-067b-45fa-9002-cd2a27376e21
-- title:
--   Brownian Iterated Construction: map step Sum eq gaussian Real
-- statement:
--   A finite Brownian step sum has the centered Gaussian law with variance equal to the squared
--   norm of its deterministic step kernel.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianWickIsometry.lean#L33-L42
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianWickIsometry.lean#L33-L42

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

theorem Malliavin.BrownianIteratedConstruction.map_stepSum_eq_gaussianReal (hB : IsPreBrownianReal B P)
    (v : ℝ≥0 →₀ ℝ) :
    P.map (stepSum B v) = gaussianReal 0 (‖stepToLp v‖₊ ^ 2) := by sorry
