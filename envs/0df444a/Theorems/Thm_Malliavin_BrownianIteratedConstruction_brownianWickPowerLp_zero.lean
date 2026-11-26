-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianWickPowerLp_zero
-- name    : Malliavin.BrownianIteratedConstruction.brownianWickPowerLp_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:05:21.020949+00:00
-- url     : https://prove2.me/theorems/3b084939-aba9-47f1-9cb7-bf04020564d1
-- title:
--   Brownian Iterated Construction: brownian Wick Power Lp zero
-- statement:
--   The zeroth Brownian Wick power is the constant-one random variable.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPolynomialHermite.lean#L63-L73
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPolynomialHermite.lean#L63-L73

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
omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W]

theorem Malliavin.BrownianIteratedConstruction.brownianWickPowerLp_zero (hB : IsPreBrownianReal B P) (v : ℝ≥0 →₀ ℝ) :
    brownianWickPowerLp hB v 0 = Lp.const 2 P (1 : ℝ) := by sorry
