-- Prove2me | Theorems.Thm_Malliavin_D12Graph_norm_eq_max
-- name    : Malliavin.D12Graph.norm_eq_max
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:07:10.941304+00:00
-- url     : https://prove2.me/theorems/17b4ae51-517a-497b-8ff6-ba57d933d9ae
-- title:
--   D12 Graph: norm eq max
-- statement:
--   The inherited complete norm is the maximum graph norm.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MalliavinDerivative.lean#L1260-L1263
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MalliavinDerivative.lean#L1260-L1263

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
open Malliavin.D12Graph

theorem Malliavin.D12Graph.norm_eq_max (F : D12Graph μ) :
    ‖F‖ = max ‖toLp μ F‖ ‖mderiv μ F‖ := by sorry
