-- Prove2me | Theorems.Thm_Malliavin_wienerIntegralEquiv_symm_ofDual
-- name    : Malliavin.wienerIntegralEquiv_symm_ofDual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:11:12.977036+00:00
-- url     : https://prove2.me/theorems/aa5a82c2-7fc0-5efa-b530-4326a89e66c0
-- title:
--   Malliavin: wiener Integral Equiv symm of Dual
-- statement:
--   `J₁⁻¹` of the Cameron--Martin generator `ofDual P (L t)` is the interval indicator
--   `1_{(0, t]}`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/TimeDerivative.lean#L510-L520
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/TimeDerivative.lean#L510-L520

import Definitions.Def_Malliavin_WienerIntegral
import Definitions.Def_Malliavin_FubiniLift
import Definitions.Def_Malliavin_MalliavinDerivative
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_TimeDerivative
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}

theorem Malliavin.wienerIntegralEquiv_symm_ofDual (hB : IsPreBrownianReal B P)
    (L : ℝ≥0 → StrongDual ℝ W) (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B)
    (t : ℝ≥0) :
    (wienerIntegralEquiv hB).symm
        (LinearIsometryEquiv.ofEq _ _ (space_eq_firstChaos hB L hL hgen) (ofDual P (L t))) =
      intervalIndicator t := by sorry
