-- Prove2me | Theorems.Thm_Malliavin_hasDerivAt_inner_mderiv
-- name    : Malliavin.hasDerivAt_inner_mderiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:05:07.959246+00:00
-- url     : https://prove2.me/theorems/2c02b5a3-924b-5f99-b339-175ce9f613e9
-- title:
--   Malliavin: has Deriv At inner mderiv
-- statement:
--   **Directional derivative characterization**: `⟪DF x, h⟫` is the derivative of `F` at `x`
--   along the Cameron--Martin direction `inclusion μ h`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MalliavinDerivative.lean#L292-L301
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MalliavinDerivative.lean#L292-L301

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_MalliavinDerivative
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]

theorem Malliavin.hasDerivAt_inner_mderiv {F : W → ℝ} {x : W} (hF : DifferentiableAt ℝ F x)
    (h : Space μ) :
    HasDerivAt (fun ε : ℝ ↦ F (x + ε • inclusion μ h)) ⟪mderiv μ F x, h⟫_ℝ 0 := by sorry
