-- Prove2me | Theorems.Thm_Malliavin_timeDerivative_mderivClosure_comp_brownian
-- name    : Malliavin.timeDerivative_mderivClosure_comp_brownian
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:13:16.34887+00:00
-- url     : https://prove2.me/theorems/c1e4b6d4-057e-4be0-83c2-3c6805f49d03
-- title:
--   Malliavin: time Derivative mderiv Closure comp brownian
-- statement:
--   **`Dₜ g (B T) = g' (B T) 1_{(0, T]}(t)`** for `C¹` functions `g` of exponential growth.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L886-L896
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L886-L896

import Definitions.Def_Malliavin_DualDerivative
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Definitions.Def_Malliavin_CylindricalGrowth
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
  (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W) (hL : ∀ t w, B t w = L t w)
include L hL
variable {g : ℝ → ℝ}

theorem Malliavin.timeDerivative_mderivClosure_comp_brownian (hgen : IsWienerGenerated B)
    (hg : ContDiff ℝ 1 g) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hgb : ∀ x, |g x| ≤ C * Real.exp (c * |x|)) (hgb' : ∀ x, |deriv g x| ≤ C * Real.exp (c * |x|))
    (T : ℝ≥0) (hd : MemLp (fun w ↦ deriv g (B T w)) 2 P) :
    timeDerivative hB L hL hgen
        (mderivClosure P ((memLp_comp_brownian L hL hg hC hc hgb T).toLp _)) =
      tensor (intervalIndicator T) (hd.toLp _) := by sorry
