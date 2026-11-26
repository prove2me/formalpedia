-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_inner_brownianWickPowerLp_of_ne
-- name    : Malliavin.BrownianIteratedConstruction.inner_brownianWickPowerLp_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:29:01.064804+00:00
-- url     : https://prove2.me/theorems/7d5a6fad-b7ab-5d49-8f8f-8a287351fa03
-- title:
--   Brownian Iterated Construction: inner brownian Wick Power Lp of ne
-- statement:
--   Wick powers of different orders of the same step sum are orthogonal.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianWickIsometry.lean#L137-L140
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianWickIsometry.lean#L137-L140

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

theorem Malliavin.BrownianIteratedConstruction.inner_brownianWickPowerLp_of_ne (hB : IsPreBrownianReal B P)
    (v : ℝ≥0 →₀ ℝ) {m n : ℕ} (hmn : m ≠ n) :
    inner ℝ (brownianWickPowerLp hB v m) (brownianWickPowerLp hB v n) = 0 := by sorry
