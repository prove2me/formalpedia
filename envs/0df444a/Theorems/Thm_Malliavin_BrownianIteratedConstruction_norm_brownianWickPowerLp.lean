-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_norm_brownianWickPowerLp
-- name    : Malliavin.BrownianIteratedConstruction.norm_brownianWickPowerLp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:29:47.192605+00:00
-- url     : https://prove2.me/theorems/ccff9ec7-3263-55d0-aff7-f38bc6bd7743
-- title:
--   Brownian Iterated Construction: norm brownian Wick Power Lp
-- statement:
--   Exact norm of a Brownian Wick power.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianWickIsometry.lean#L180-L193
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianWickIsometry.lean#L180-L193

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

theorem Malliavin.BrownianIteratedConstruction.norm_brownianWickPowerLp (hB : IsPreBrownianReal B P)
    (v : ℝ≥0 →₀ ℝ) (n : ℕ) :
    ‖brownianWickPowerLp hB v n‖ =
      Real.sqrt (n.factorial : ℝ) * ‖stepToLp v‖ ^ n := by sorry
