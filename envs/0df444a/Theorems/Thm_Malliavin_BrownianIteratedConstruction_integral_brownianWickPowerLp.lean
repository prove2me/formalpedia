-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_integral_brownianWickPowerLp
-- name    : Malliavin.BrownianIteratedConstruction.integral_brownianWickPowerLp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:19:32.020881+00:00
-- url     : https://prove2.me/theorems/3dbaa65f-547e-4258-aeeb-1ccd43e23074
-- title:
--   Brownian Iterated Construction: integral brownian Wick Power Lp
-- statement:
--   Every positive-order Brownian Wick power is centered.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianWickIsometry.lean#L154-L175
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianWickIsometry.lean#L154-L175

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

theorem Malliavin.BrownianIteratedConstruction.integral_brownianWickPowerLp (hB : IsPreBrownianReal B P)
    (v : ℝ≥0 →₀ ℝ) {n : ℕ} (hn : 0 < n) :
    ∫ w, brownianWickPowerLp hB v n w ∂P = 0 := by sorry
