-- Prove2me | Theorems.Thm_Malliavin_centeredWienerIntegral_coe
-- name    : Malliavin.centeredWienerIntegral_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:49:25.634683+00:00
-- url     : https://prove2.me/theorems/431fe378-c9c4-49b9-9fc9-b438c081e268
-- title:
--   Malliavin: centered Wiener Integral coe
-- statement:
--   The ambient value of `centeredWienerIntegral` is the Wiener integral.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoRange.lean#L242-L246
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoRange.lean#L242-L246

import Definitions.Def_Malliavin_ItoConsequences
import Definitions.Def_Malliavin_NaturalItoRange
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

theorem Malliavin.centeredWienerIntegral_coe
    (hB : IsPreBrownianReal B P)
    (g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    (centeredWienerIntegral hB g : RandomL2 P) = wienerIntegral hB g := by sorry

attribute [defeq] Malliavin.centeredWienerIntegral_coe
