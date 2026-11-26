-- Prove2me | Theorems.Thm_Malliavin_norm_sub_expectationL2
-- name    : Malliavin.norm_sub_expectationL2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:18:46.9256+00:00
-- url     : https://prove2.me/theorems/c46f3454-b8e7-4aa1-b8f8-f792766ffba7
-- title:
--   Malliavin: norm sub expectation L2
-- statement:
--   Isometric norm identity for the centered abstract representation.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOcone.lean#L844-L848
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOcone.lean#L844-L848

import Definitions.Def_Malliavin_TimeDerivative
import Mathlib.Probability.Process.Predictable
import Definitions.Def_Malliavin_ClarkOcone
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}

theorem Malliavin.norm_sub_expectationL2 {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) (F : D12 P) :
    ‖F.1 - expectationL2 F.1‖ = ‖predictableDerivative C F‖ := by sorry
