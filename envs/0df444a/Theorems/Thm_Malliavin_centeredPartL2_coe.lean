-- Prove2me | Theorems.Thm_Malliavin_centeredPartL2_coe
-- name    : Malliavin.centeredPartL2_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:45:48.475855+00:00
-- url     : https://prove2.me/theorems/3cd9c58f-9658-5201-a41b-f7036a8a5d92
-- title:
--   Malliavin: centered Part L2 coe
-- statement:
--   The ambient value of `centeredPartL2 G` is `G - E[G]`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoRange.lean#L144-L146
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoRange.lean#L144-L146

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

theorem Malliavin.centeredPartL2_coe (G : RandomL2 P) :
    (centeredPartL2 G : RandomL2 P) = G - expectationL2 G := by sorry

attribute [defeq] Malliavin.centeredPartL2_coe
