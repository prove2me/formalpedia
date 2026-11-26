-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_inner_brownianWickPowerLp_chainIntegralLp_eq_purePower
-- name    : Malliavin.BrownianIteratedConstruction.inner_brownianWickPowerLp_chainIntegralLp_eq_purePower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:23:12.585952+00:00
-- url     : https://prove2.me/theorems/70127df4-a403-4dd6-b1ab-385c24956a4f
-- title:
--   Brownian Iterated Construction: inner brownian Wick Power Lp chain Integral Lp eq pure Power
-- statement:
--   Wick and canonical pure-power values induce the same linear functional on every ordered
--   chain of the matching order.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerDuality.lean#L318-L328
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerDuality.lean#L318-L328

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

theorem Malliavin.BrownianIteratedConstruction.inner_brownianWickPowerLp_chainIntegralLp_eq_purePower
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B) (hsm : ∀ t, StronglyMeasurable (B t))
    (v : ℝ≥0 →₀ ℝ) {n : ℕ} (a : OrderedBoxIndex n) :
    inner ℝ (brownianWickPowerLp hB v n) (chainIntegralLp hB a.u a.v) =
      inner ℝ (brownianPurePowerIntegral hB n (stepToLp v))
        (chainIntegralLp hB a.u a.v) := by sorry
