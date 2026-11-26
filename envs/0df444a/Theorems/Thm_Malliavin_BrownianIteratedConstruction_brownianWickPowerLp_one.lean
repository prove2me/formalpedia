-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianWickPowerLp_one
-- name    : Malliavin.BrownianIteratedConstruction.brownianWickPowerLp_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:08:36.042334+00:00
-- url     : https://prove2.me/theorems/46994eed-51c1-58c6-97f5-8429730d5cf6
-- title:
--   Brownian Iterated Construction: brownian Wick Power Lp one
-- statement:
--   The first Brownian Wick power is its finite Brownian step sum in `L²`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPolynomialHermite.lean#L78-L88
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPolynomialHermite.lean#L78-L88

import Definitions.Def_Malliavin_BrownianHermite
import Definitions.Def_Malliavin_BrownianCylinderDensity
import Definitions.Def_Malliavin_BrownianChaosTotality
import Definitions.Def_Malliavin_BrownianPolynomialHermite
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin Malliavin.BrownianIteratedConstruction
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P]

theorem Malliavin.BrownianIteratedConstruction.brownianWickPowerLp_one (hB : IsPreBrownianReal B P) (v : ℝ≥0 →₀ ℝ) :
    brownianWickPowerLp hB v 1 = stepToRandom hB v := by sorry
