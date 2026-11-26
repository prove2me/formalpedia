-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_timeDerivative_mderivClosure_brownianWickPowerLp
-- name    : Malliavin.BrownianIteratedConstruction.timeDerivative_mderivClosure_brownianWickPowerLp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:22:38.160772+00:00
-- url     : https://prove2.me/theorems/db8317ab-24f3-4440-91a8-d52c798a98df
-- title:
--   Brownian Iterated Construction: time Derivative mderiv Closure brownian Wick Power Lp
-- statement:
--   The time-realized Malliavin derivative of a Wick power is its predecessor tensored with the
--   deterministic step kernel.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerDuality.lean#L114-L170
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerDuality.lean#L114-L170

import Definitions.Def_Malliavin_BrownianWickPurePowerComparison
import Definitions.Def_Malliavin_BrownianMultipleIntegralBoxSpan
import Definitions.Def_Malliavin_PastCylinderDensity
import Definitions.Def_Malliavin_BrownianPurePowerDuality
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

theorem Malliavin.BrownianIteratedConstruction.timeDerivative_mderivClosure_brownianWickPowerLp
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B) (v : ℝ≥0 →₀ ℝ) (n : ℕ) :
    timeDerivative hB coordinate coordinate_apply generated
        (mderivClosure P (brownianWickPowerLp hB v n)) =
      tensor (stepToLp v) ((n : ℝ) • brownianWickPowerLp hB v (n - 1)) := by sorry
