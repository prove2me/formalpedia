-- Prove2me | Theorems.Thm_Malliavin_cylinderPartialExp_oneCoord
-- name    : Malliavin.cylinderPartialExp_oneCoord
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:26:05.570352+00:00
-- url     : https://prove2.me/theorems/5dcaff0f-4d07-47a5-a614-25b9a4d19c4e
-- title:
--   Malliavin: cylinder Partial Exp one Coord
-- statement:
--   The partial derivative of `y ↦ g (y 0)` at the Brownian coordinate is `g' (B T)`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L871-L883
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L871-L883

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

theorem Malliavin.cylinderPartialExp_oneCoord (hg : ContDiff ℝ 1 g) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hgb' : ∀ x, |deriv g x| ≤ C * Real.exp (c * |x|)) (T : ℝ≥0)
    (hd : MemLp (fun w ↦ deriv g (B T w)) 2 P) :
    cylinderPartialExp (P := P) L hL (contDiff_oneCoord hg) hC hc
        (norm_fderiv_oneCoord_le hg hC hc hgb') (fun _ ↦ T) 0 =
      hd.toLp _ := by sorry
