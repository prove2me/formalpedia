-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_inner_brownianPurePowerIntegral_chainIntegralLp
-- name    : Malliavin.BrownianIteratedConstruction.inner_brownianPurePowerIntegral_chainIntegralLp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:22:33.387021+00:00
-- url     : https://prove2.me/theorems/370aa8e3-6ffb-4ecb-af74-0c4de067a8c7
-- title:
--   Brownian Iterated Construction: inner brownian Pure Power Integral chain Integral Lp
-- statement:
--   The canonical pure-power multiple integral has the same pairing with every ordered Brownian
--   increment chain.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerDuality.lean#L303-L314
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerDuality.lean#L303-L314

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
omit [CompleteSpace W] [BorelSpace W]

theorem Malliavin.BrownianIteratedConstruction.inner_brownianPurePowerIntegral_chainIntegralLp
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) {n : ℕ} (a : OrderedBoxIndex n) :
    inner ℝ (brownianPurePowerIntegral hB n f) (chainIntegralLp hB a.u a.v) =
      (n.factorial : ℝ) *
        ∏ i, inner ℝ f (iocIndicator (a.u i) (a.v i)) := by sorry
