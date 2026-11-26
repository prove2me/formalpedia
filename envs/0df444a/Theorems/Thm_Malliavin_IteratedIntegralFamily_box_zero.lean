-- Prove2me | Theorems.Thm_Malliavin_IteratedIntegralFamily_box_zero
-- name    : Malliavin.IteratedIntegralFamily.box_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:52:19.008273+00:00
-- url     : https://prove2.me/theorems/3224540f-d275-5cfe-a332-fda8b78b7b10
-- title:
--   Iterated Integral Family: box zero
-- statement:
--   The order-zero clause of the Brownian link holds for every family: the order-zero kernel
--   space is one-dimensional and `zeroOrder` identifies `J₀` with the integral.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L395-L407
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L395-L407

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.IteratedIntegralFamily.box_zero (J : IteratedIntegralFamily P) (u v : Fin 0 → ℝ≥0) :
    (fun ω ↦ J.integral 0 (boxKernel u v) ω) =ᵐ[P] chainIntegral B u v := by sorry
