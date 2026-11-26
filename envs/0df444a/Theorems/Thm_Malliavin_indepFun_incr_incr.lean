-- Prove2me | Theorems.Thm_Malliavin_indepFun_incr_incr
-- name    : Malliavin.indepFun_incr_incr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:54:07.137359+00:00
-- url     : https://prove2.me/theorems/9bd54fb3-d4f1-40e5-a1b5-554872360bb4
-- title:
--   Malliavin: indep Fun incr incr
-- statement:
--   Increments over consecutive disjoint intervals are independent.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L698-L707
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L698-L707

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.indepFun_incr_incr (hB : IsPreBrownianReal B P) {a b c d : ℝ≥0} (hab : a ≤ b)
    (hbc : b ≤ c) (hcd : c ≤ d) :
    IndepFun (fun ω ↦ B b ω - B a ω) (fun ω ↦ B d ω - B c ω) P := by sorry
