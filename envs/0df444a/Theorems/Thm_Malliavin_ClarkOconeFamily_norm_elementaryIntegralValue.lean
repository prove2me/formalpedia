-- Prove2me | Theorems.Thm_Malliavin_ClarkOconeFamily_norm_elementaryIntegralValue
-- name    : Malliavin.ClarkOconeFamily.norm_elementaryIntegralValue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:30:03.672402+00:00
-- url     : https://prove2.me/theorems/4a14a9ab-d040-56b4-9173-ba9cb0a0af1a
-- title:
--   Clark Ocone Family: norm elementary Integral Value
-- statement:
--   The elementary compatibility formula satisfies the expected product-norm Itô isometry.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOcone.lean#L612-L652
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOcone.lean#L612-L652

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

theorem Malliavin.ClarkOconeFamily.norm_elementaryIntegralValue
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} (C : ClarkOconeFamily B P 𝓕)
    {a b : ℝ≥0} (hab : a ≤ b) (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    ‖C.elementaryIntegralValue hab Z‖ = ‖iocIndicator a b‖ * ‖(Z : RandomL2 P)‖ := by sorry
