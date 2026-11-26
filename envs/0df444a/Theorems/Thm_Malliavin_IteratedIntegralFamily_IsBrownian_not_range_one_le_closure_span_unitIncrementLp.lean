-- Prove2me | Theorems.Thm_Malliavin_IteratedIntegralFamily_IsBrownian_not_range_one_le_closure_span_unitIncrementLp
-- name    : Malliavin.IteratedIntegralFamily.IsBrownian.not_range_one_le_closure_span_unitIncrementLp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:03:39.7118+00:00
-- url     : https://prove2.me/theorems/b91b57df-2fef-5f1f-8a33-bfa6898b2e43
-- title:
--   Is Brownian: not range one le closure span unit Increment Lp
-- statement:
--   **No family satisfying the Brownian link has its order-one range inside the closed span of
--   the unit increments** `B (k + 1) - B k`: the order-one operator is the Wiener integral, whose
--   range contains `B (1/2)`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L1075-L1086
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L1075-L1086

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.IteratedIntegralFamily.IsBrownian.not_range_one_le_closure_span_unitIncrementLp
    {J : IteratedIntegralFamily P} (hJ : J.IsBrownian B) (hB : IsPreBrownianReal B P) :
    ¬ LinearMap.range (J.integral 1).toLinearMap ≤
      (Submodule.span ℝ (Set.range (unitIncrementLp hB))).topologicalClosure := by sorry
