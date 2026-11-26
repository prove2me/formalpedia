-- Prove2me | Theorems.Thm_Malliavin_ClarkOconeFamily_norm_timeDerivative
-- name    : Malliavin.ClarkOconeFamily.norm_timeDerivative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:20:37.825668+00:00
-- url     : https://prove2.me/theorems/689e4462-544d-5795-9ada-19a8240883a7
-- title:
--   Clark Ocone Family: norm time Derivative
-- statement:
--   The time derivative preserves the `L²(Ω; H)` norm.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOcone.lean#L456-L460
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOcone.lean#L456-L460

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

theorem Malliavin.ClarkOconeFamily.norm_timeDerivative {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) (U : Lp (CameronMartin.Space P) 2 P) :
    ‖C.timeDerivative U‖ = ‖U‖ := by sorry
