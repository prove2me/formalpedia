-- Prove2me | Theorems.Thm_Malliavin_mderivClosure_toLp
-- name    : Malliavin.mderivClosure_toLp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:05:03.889632+00:00
-- url     : https://prove2.me/theorems/295bc8ef-7b61-572b-90ec-3b7ae1df19f0
-- title:
--   Malliavin: mderiv Closure to Lp
-- statement:
--   The closed extension agrees with `D` on smooth bounded functionals.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MalliavinDerivative.lean#L1030-L1032
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MalliavinDerivative.lean#L1030-L1032

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

theorem Malliavin.mderivClosure_toLp {F : W → ℝ} (hF : IsSmoothBounded F) :
    mderivClosure μ (hF.toLp μ) = hF.mderivLp μ := by sorry
