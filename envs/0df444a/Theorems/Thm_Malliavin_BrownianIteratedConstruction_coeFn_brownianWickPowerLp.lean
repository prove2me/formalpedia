-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_coeFn_brownianWickPowerLp
-- name    : Malliavin.BrownianIteratedConstruction.coeFn_brownianWickPowerLp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:04:01.101233+00:00
-- url     : https://prove2.me/theorems/29c0838c-33ff-5d39-a0ba-6bd12e83b832
-- title:
--   Brownian Iterated Construction: coe Fn brownian Wick Power Lp
-- statement:
--   The Brownian Wick-power construction represents pointwise generalized Hermite evaluation.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPolynomialHermite.lean#L42-L48
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPolynomialHermite.lean#L42-L48

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

theorem Malliavin.BrownianIteratedConstruction.coeFn_brownianWickPowerLp (hB : IsPreBrownianReal B P)
    (v : ℝ≥0 →₀ ℝ) (n : ℕ) :
    (brownianWickPowerLp hB v n : W → ℝ) =ᵐ[P]
      fun w ↦ (varianceHermite (‖stepToLp v‖ ^ 2) n).eval (stepSum B v w) := by sorry
