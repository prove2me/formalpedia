-- Prove2me | Theorems.Thm_Malliavin_IteratedIntegralFamily_IsBrownian_integral_two_boxKernel
-- name    : Malliavin.IteratedIntegralFamily.IsBrownian.integral_two_boxKernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:53:57.635124+00:00
-- url     : https://prove2.me/theorems/80892944-eb51-4903-9a98-dc9d8cbd426f
-- title:
--   Is Brownian: integral two box Kernel
-- statement:
--   For a Brownian family, the order-two operator sends the indicator of an ordered box
--   `(a, b] × (c, d]` to the product of increments `(B b - B a) (B d - B c)`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L945-L959
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L945-L959

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.IteratedIntegralFamily.IsBrownian.integral_two_boxKernel {J : IteratedIntegralFamily P}
    (hJ : J.IsBrownian B) (hB : IsPreBrownianReal B P) {a b c d : ℝ≥0} (hab : a ≤ b)
    (hbc : b ≤ c) (hcd : c ≤ d) :
    J.integral 2 (boxKernel ![a, c] ![b, d]) = incrementProductLp hB a b c d := by sorry
