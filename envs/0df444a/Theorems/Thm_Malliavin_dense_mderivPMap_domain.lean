-- Prove2me | Theorems.Thm_Malliavin_dense_mderivPMap_domain
-- name    : Malliavin.dense_mderivPMap_domain
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:07:05.829662+00:00
-- url     : https://prove2.me/theorems/aec75692-1802-53ec-8f4a-9b01bbf3ece9
-- title:
--   Malliavin: dense mderiv PMap domain
-- statement:
--   The closed Malliavin derivative is densely defined as a partial linear map.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MalliavinDerivative.lean#L1219-L1222
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MalliavinDerivative.lean#L1219-L1222

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

theorem Malliavin.dense_mderivPMap_domain :
    Dense ((mderivPMap μ).domain : Set (Lp ℝ 2 μ)) := by sorry
