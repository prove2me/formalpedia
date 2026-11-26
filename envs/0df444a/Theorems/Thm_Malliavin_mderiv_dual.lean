-- Prove2me | Theorems.Thm_Malliavin_mderiv_dual
-- name    : Malliavin.mderiv_dual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:05:33.407805+00:00
-- url     : https://prove2.me/theorems/3a97f5bf-8631-551f-88e0-bcdf5f5f7e05
-- title:
--   Malliavin: mderiv dual
-- statement:
--   The derivative of a continuous linear functional is its Cameron--Martin generator.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MalliavinDerivative.lean#L359-L362
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MalliavinDerivative.lean#L359-L362

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

theorem Malliavin.mderiv_dual (L : StrongDual ℝ W) (x : W) : mderiv μ (⇑L) x = ofDual μ L := by sorry
