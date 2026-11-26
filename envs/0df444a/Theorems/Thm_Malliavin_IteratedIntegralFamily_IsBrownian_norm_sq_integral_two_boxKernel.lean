-- Prove2me | Theorems.Thm_Malliavin_IteratedIntegralFamily_IsBrownian_norm_sq_integral_two_boxKernel
-- name    : Malliavin.IteratedIntegralFamily.IsBrownian.norm_sq_integral_two_boxKernel
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:03:28.596428+00:00
-- url     : https://prove2.me/theorems/5338be9f-5a25-521d-9472-1ceee81073af
-- title:
--   Is Brownian: norm sq integral two box Kernel
-- statement:
--   For a Brownian-linked family, the conditional order-two box value has squared norm
--   `(b - a) (d - c)`.  The norm formula itself is already an instance of
--   `IteratedIntegralFamily.norm_sq_integral_boxKernel`; the Brownian hypothesis is needed for the
--   preceding increment-product value identity.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L965-L969
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L965-L969

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.IteratedIntegralFamily.IsBrownian.norm_sq_integral_two_boxKernel
    {J : IteratedIntegralFamily P} (hJ : J.IsBrownian B) (hB : IsPreBrownianReal B P)
    {a b c d : ℝ≥0} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    ‖J.integral 2 (boxKernel ![a, c] ![b, d])‖ ^ 2 = ((b : ℝ) - a) * ((d : ℝ) - c) := by sorry
