-- Prove2me | Theorems.Thm_Malliavin_simpleVec_one
-- name    : Malliavin.simpleVec_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:06:06.706265+00:00
-- url     : https://prove2.me/theorems/91e800e4-bc5c-5799-9c60-4d13b203de46
-- title:
--   Malliavin: simple Vec one
-- statement:
--   The simple vector `1 • h` is the constant `h`, and its divergence is `h` itself.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MalliavinDerivative.lean#L1333-L1338
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MalliavinDerivative.lean#L1333-L1338

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
omit [CompleteSpace W]

theorem Malliavin.simpleVec_one (h : Space μ) :
    simpleVec μ (⟨fun _ ↦ 1, IsSmoothBounded.const 1⟩, h) =
      (memLp_const h).toLp (fun _ ↦ h) := by sorry
