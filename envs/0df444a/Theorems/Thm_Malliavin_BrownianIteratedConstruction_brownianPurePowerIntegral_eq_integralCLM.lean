-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianPurePowerIntegral_eq_integralCLM
-- name    : Malliavin.BrownianIteratedConstruction.brownianPurePowerIntegral_eq_integralCLM
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:08:30.197115+00:00
-- url     : https://prove2.me/theorems/a4cb441a-671b-5229-bbc0-602c84c68ccc
-- title:
--   Brownian Iterated Construction: brownian Pure Power Integral eq integral CLM
-- statement:
--   Symmetry of a pure-power kernel removes symmetrization from its multiple integral.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerIntegral.lean#L39-L45
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerIntegral.lean#L39-L45

import Definitions.Def_Malliavin_IteratedKernelPurePower
import Definitions.Def_Malliavin_BrownianPolynomialHermite
import Definitions.Def_Malliavin_BrownianPurePowerIntegral
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

theorem Malliavin.BrownianIteratedConstruction.brownianPurePowerIntegral_eq_integralCLM
    (hB : IsPreBrownianReal B P) (n : ℕ)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    brownianPurePowerIntegral hB n f =
      (n.factorial : ℝ) • integralCLM hB n (iteratedKernelPurePower n f) := by sorry
