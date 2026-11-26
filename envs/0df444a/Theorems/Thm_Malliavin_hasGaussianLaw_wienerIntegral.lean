-- Prove2me | Theorems.Thm_Malliavin_hasGaussianLaw_wienerIntegral
-- name    : Malliavin.hasGaussianLaw_wienerIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:52:15.606076+00:00
-- url     : https://prove2.me/theorems/5f5b633d-794f-421c-acc8-204893283ec7
-- title:
--   Malliavin: has Gaussian Law wiener Integral
-- statement:
--   **Wiener integrals are Gaussian.**
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L809-L820
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L809-L820

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
open CameronMartin

theorem Malliavin.hasGaussianLaw_wienerIntegral (hB : IsPreBrownianReal B P)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    HasGaussianLaw (wienerIntegral hB f : Ω → ℝ) P := by sorry
