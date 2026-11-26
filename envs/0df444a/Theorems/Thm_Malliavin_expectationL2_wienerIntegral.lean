-- Prove2me | Theorems.Thm_Malliavin_expectationL2_wienerIntegral
-- name    : Malliavin.expectationL2_wienerIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:37:40.969314+00:00
-- url     : https://prove2.me/theorems/ed8743f4-6596-4035-a4b0-38987e8e0a29
-- title:
--   Malliavin: expectation L2 wiener Integral
-- statement:
--   A Wiener integral has zero expectation, stated in the `RandomL2` API used by Clark--Ocone.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoDuality.lean#L47-L52
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoDuality.lean#L47-L52

import Definitions.Def_Malliavin_NaturalItoRange
import Definitions.Def_Malliavin_ClarkOconeExamples
import Definitions.Def_Malliavin_NaturalItoDuality
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W]

theorem Malliavin.expectationL2_wienerIntegral
    (hB : IsPreBrownianReal B P) (g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    expectationL2 (wienerIntegral hB g) = 0 := by sorry
