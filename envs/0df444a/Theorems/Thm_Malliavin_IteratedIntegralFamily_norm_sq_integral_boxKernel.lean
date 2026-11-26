-- Prove2me | Theorems.Thm_Malliavin_IteratedIntegralFamily_norm_sq_integral_boxKernel
-- name    : Malliavin.IteratedIntegralFamily.norm_sq_integral_boxKernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:59:48.518655+00:00
-- url     : https://prove2.me/theorems/fb78ed67-2d8d-5956-a0fe-db233a635e8f
-- title:
--   Iterated Integral Family: norm sq integral box Kernel
-- statement:
--   The Hilbert-space `sameOrder` law alone fixes the squared norm of every ordered-box image.
--   Brownian ordered-box compatibility is not needed for this norm identity.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L422-L460
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L422-L460

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.IteratedIntegralFamily.norm_sq_integral_boxKernel (J : IteratedIntegralFamily P)
    {n : ℕ} (u v : Fin n → ℝ≥0) (huv : ∀ i, u i ≤ v i)
    (hord : ∀ i j, i < j → v i ≤ u j) :
    ‖J.integral n (boxKernel u v)‖ ^ 2 = ∏ i, ((v i : ℝ) - u i) := by sorry
