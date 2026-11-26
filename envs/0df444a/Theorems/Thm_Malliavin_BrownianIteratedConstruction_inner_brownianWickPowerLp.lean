-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_inner_brownianWickPowerLp
-- name    : Malliavin.BrownianIteratedConstruction.inner_brownianWickPowerLp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:09:00.07349+00:00
-- url     : https://prove2.me/theorems/9e6003ab-3ae4-4c65-8217-f58859218c67
-- title:
--   Brownian Iterated Construction: inner brownian Wick Power Lp
-- statement:
--   Wick powers of one finite Brownian step sum are orthogonal, with the usual factorial norm.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianWickIsometry.lean#L102-L132
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianWickIsometry.lean#L102-L132

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

theorem Malliavin.BrownianIteratedConstruction.inner_brownianWickPowerLp (hB : IsPreBrownianReal B P)
    (v : ℝ≥0 →₀ ℝ) (m n : ℕ) :
    inner ℝ (brownianWickPowerLp hB v m) (brownianWickPowerLp hB v n) =
      if m = n then m.factorial * (‖stepToLp v‖ ^ 2) ^ m else 0 := by sorry
