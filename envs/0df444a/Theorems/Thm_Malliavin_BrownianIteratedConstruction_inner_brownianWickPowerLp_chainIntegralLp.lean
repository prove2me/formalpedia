-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_inner_brownianWickPowerLp_chainIntegralLp
-- name    : Malliavin.BrownianIteratedConstruction.inner_brownianWickPowerLp_chainIntegralLp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:25:06.183542+00:00
-- url     : https://prove2.me/theorems/4816202b-c2be-44de-91cd-a3cc439144d3
-- title:
--   Brownian Iterated Construction: inner brownian Wick Power Lp chain Integral Lp
-- statement:
--   Recursive Malliavin--Itô duality computes the pairing of an order-`n` Wick power with an
--   ordered Brownian increment chain.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerDuality.lean#L236-L298
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerDuality.lean#L236-L298

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

theorem Malliavin.BrownianIteratedConstruction.inner_brownianWickPowerLp_chainIntegralLp
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B) (hsm : ∀ t, StronglyMeasurable (B t))
    (v : ℝ≥0 →₀ ℝ) {n : ℕ} (a : OrderedBoxIndex n) :
    inner ℝ (brownianWickPowerLp hB v n) (chainIntegralLp hB a.u a.v) =
      (n.factorial : ℝ) *
        ∏ i, inner ℝ (stepToLp v) (iocIndicator (a.u i) (a.v i)) := by sorry
