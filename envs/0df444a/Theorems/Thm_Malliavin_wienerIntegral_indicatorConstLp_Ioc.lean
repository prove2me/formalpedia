-- Prove2me | Theorems.Thm_Malliavin_wienerIntegral_indicatorConstLp_Ioc
-- name    : Malliavin.wienerIntegral_indicatorConstLp_Ioc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:52:16.692716+00:00
-- url     : https://prove2.me/theorems/a5059473-a840-53f9-9da7-94ab0e72c026
-- title:
--   Malliavin: wiener Integral indicator Const Lp Ioc
-- statement:
--   `J₁ (1_{(a, b]}) = B b - B a`: the Wiener integral of an interval indicator is the Brownian
--   increment.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L285-L298
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L285-L298

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.wienerIntegral_indicatorConstLp_Ioc (hB : IsPreBrownianReal B P) {a b : ℝ≥0}
    (hab : a ≤ b) :
    wienerIntegral hB (indicatorConstLp 2 measurableSet_Ioc
      (nonnegativeLebesgueMeasure_Ioc_ne_top a b) (1 : ℝ)) = brownianLp hB b - brownianLp hB a := by sorry
