-- Prove2me | Theorems.Thm_Malliavin_timeDerivative_mderivClosure_wienerIntegral
-- name    : Malliavin.timeDerivative_mderivClosure_wienerIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:13:44.33092+00:00
-- url     : https://prove2.me/theorems/77eb90d1-4382-4512-b49b-94a6b8415fc8
-- title:
--   Malliavin: time Derivative mderiv Closure wiener Integral
-- statement:
--   **`Dₜ (∫ g dB) = g(t)`**: the time derivative of a Wiener integral is the deterministic
--   process `(t, ω) ↦ g t`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/DualDerivative.lean#L415-L425
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/DualDerivative.lean#L415-L425

import Definitions.Def_Malliavin_TimeDerivative
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_DualDerivative
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}

theorem Malliavin.timeDerivative_mderivClosure_wienerIntegral (hB : IsPreBrownianReal B P)
    (L : ℝ≥0 → StrongDual ℝ W) (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B)
    (g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    timeDerivative hB L hL hgen (mderivClosure P (wienerIntegral hB g)) =
      tensor g (Lp.const 2 P (1 : ℝ)) := by sorry
