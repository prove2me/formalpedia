-- Prove2me | Theorems.Thm_Malliavin_inner_incrementProductLp_wienerIntegral
-- name    : Malliavin.inner_incrementProductLp_wienerIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:53:07.677364+00:00
-- url     : https://prove2.me/theorems/8e87acbd-1c86-58df-ba50-d8cf63560b08
-- title:
--   Malliavin: inner increment Product Lp wiener Integral
-- statement:
--   **Products of increments are orthogonal to the first chaos**: for every `f ∈ L²(ℝ≥0)`,
--   `E[(B b - B a) (B d - B c) J₁ f] = 0`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L666-L675
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L666-L675

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.inner_incrementProductLp_wienerIntegral (hB : IsPreBrownianReal B P) (a b c d : ℝ≥0)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    ⟪incrementProductLp hB a b c d, wienerIntegral hB f⟫_ℝ = 0 := by sorry
