-- Prove2me | Theorems.Thm_Malliavin_IteratedIntegralFamily_IsBrownian_of_pos
-- name    : Malliavin.IteratedIntegralFamily.IsBrownian.of_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:59:39.389874+00:00
-- url     : https://prove2.me/theorems/531d71c3-5b81-565e-b2f6-3ef82842290d
-- title:
--   Is Brownian: of pos
-- statement:
--   To be Brownian it suffices to satisfy the box law at positive orders.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L410-L418
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L410-L418

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.IteratedIntegralFamily.IsBrownian.of_pos {J : IteratedIntegralFamily P}
    (h : ∀ (n : ℕ), 0 < n → ∀ (u v : Fin n → ℝ≥0), (∀ i, u i ≤ v i) →
      (∀ i j, i < j → v i ≤ u j) →
      (fun ω ↦ J.integral n (boxKernel u v) ω) =ᵐ[P] chainIntegral B u v) :
    J.IsBrownian B := by sorry
