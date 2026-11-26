-- Prove2me | Theorems.Thm_Malliavin_norm_firstChaos_starProjection_le_mderivClosure
-- name    : Malliavin.norm_firstChaos_starProjection_le_mderivClosure
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:08:13.338712+00:00
-- url     : https://prove2.me/theorems/637846e3-51a0-45dd-9cfa-7aaaf378d634
-- title:
--   Malliavin: norm first Chaos star Projection le mderiv Closure
-- statement:
--   The first-chaos component of a Sobolev functional is controlled by its closed Malliavin
--   derivative.  This is the order-one part of the Gaussian Poincaré estimate.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MalliavinDerivative.lean#L1358-L1389
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MalliavinDerivative.lean#L1358-L1389

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

theorem Malliavin.norm_firstChaos_starProjection_le_mderivClosure
    {F : Lp ℝ 2 μ} (hF : F ∈ domD12 μ) :
    ‖(firstChaos μ).starProjection F‖ ≤ ‖mderivClosure μ F‖ := by sorry
