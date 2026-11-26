-- Prove2me | Theorems.Thm_Malliavin_norm_mderiv_comp_truncCoord_le
-- name    : Malliavin.norm_mderiv_comp_truncCoord_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:25:14.074893+00:00
-- url     : https://prove2.me/theorems/de4a49f2-4ab6-51d5-b79a-b3dee230c6c6
-- title:
--   Malliavin: norm mderiv comp trunc Coord le
-- statement:
--   Pointwise bound for the Malliavin derivative of a truncated cylindrical functional, in
--   terms of a dominating function `φ ≥ ‖f'‖`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L209-L227
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L209-L227

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
  (μ : Measure W) [IsGaussian μ]

theorem Malliavin.norm_mderiv_comp_truncCoord_le {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    {φ : (Fin n → ℝ) → ℝ} (hφ : ∀ y, ‖fderiv ℝ f y‖ ≤ φ y) (m : ℕ)
    (L : Fin n → StrongDual ℝ W) (x : W) :
    ‖mderiv μ (fun y ↦ f (truncCoord m L y)) x‖ ≤
      φ (truncCoord m L x) * ∑ i, ‖ofDual μ (L i)‖ := by sorry
