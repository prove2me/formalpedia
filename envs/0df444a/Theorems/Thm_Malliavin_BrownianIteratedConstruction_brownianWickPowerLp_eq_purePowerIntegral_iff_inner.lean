-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianWickPowerLp_eq_purePowerIntegral_iff_inner
-- name    : Malliavin.BrownianIteratedConstruction.brownianWickPowerLp_eq_purePowerIntegral_iff_inner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:11:48.245257+00:00
-- url     : https://prove2.me/theorems/b5bab0e0-23e5-430e-8ab8-6c66c93844ad
-- title:
--   Brownian Iterated Construction: brownian Wick Power Lp eq pure Power Integral iff inner
-- statement:
--   Equality of a Wick power and its canonical pure-power multiple integral is equivalent to
--   their mixed inner product attaining their common squared norm.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianWickPurePowerComparison.lean#L34-L66
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianWickPurePowerComparison.lean#L34-L66

import Definitions.Def_Malliavin_BrownianWickIsometry
import Definitions.Def_Malliavin_BrownianPurePowerRecurrence
import Definitions.Def_Malliavin_BrownianWickPurePowerComparison
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
omit [CompleteSpace W] [BorelSpace W]

theorem Malliavin.BrownianIteratedConstruction.brownianWickPowerLp_eq_purePowerIntegral_iff_inner
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (v : ℝ≥0 →₀ ℝ) (n : ℕ) :
    brownianWickPowerLp hB v n =
        brownianPurePowerIntegral hB n (stepToLp v) ↔
      inner ℝ (brownianWickPowerLp hB v n)
          (brownianPurePowerIntegral hB n (stepToLp v)) =
        (n.factorial : ℝ) * (‖stepToLp v‖ ^ 2) ^ n := by sorry
