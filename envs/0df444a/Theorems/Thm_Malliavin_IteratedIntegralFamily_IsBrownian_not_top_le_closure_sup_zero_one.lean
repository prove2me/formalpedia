-- Prove2me | Theorems.Thm_Malliavin_IteratedIntegralFamily_IsBrownian_not_top_le_closure_sup_zero_one
-- name    : Malliavin.IteratedIntegralFamily.IsBrownian.not_top_le_closure_sup_zero_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:01:55.166132+00:00
-- url     : https://prove2.me/theorems/fe953b87-70a9-5558-bf83-738853d68a37
-- title:
--   Is Brownian: not top le closure sup zero one
-- statement:
--   **Orders zero and one never exhaust `L²(P)`** for a family satisfying the Brownian link:
--   `(B 1 - B 0)(B 2 - B 1)` is orthogonal to both.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L902-L922
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L902-L922

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.IteratedIntegralFamily.IsBrownian.not_top_le_closure_sup_zero_one
    {J : IteratedIntegralFamily P} (hJ : J.IsBrownian B) (hB : IsPreBrownianReal B P) :
    ¬ (⊤ : Submodule ℝ (RandomL2 P)) ≤
      (LinearMap.range (J.integral 0).toLinearMap ⊔
        LinearMap.range (J.integral 1).toLinearMap).topologicalClosure := by sorry
