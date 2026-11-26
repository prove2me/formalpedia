-- Prove2me | Theorems.Thm_Malliavin_IteratedIntegralFamily_IsBrownian_integral_one_eq
-- name    : Malliavin.IteratedIntegralFamily.IsBrownian.integral_one_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:51:23.130961+00:00
-- url     : https://prove2.me/theorems/084cf462-fe99-4ae6-8114-9003b0dd829d
-- title:
--   Is Brownian: integral one eq
-- statement:
--   **Uniqueness of the order-one level.**  Any family of operators satisfying the Brownian link
--   has the Wiener integral as its order-one operator.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L561-L569
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/WienerIntegral.lean#L561-L569

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_WienerIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.IteratedIntegralFamily.IsBrownian.integral_one_eq {J : IteratedIntegralFamily P}
    (hJ : J.IsBrownian B) (hB : IsPreBrownianReal B P) :
    J.integral 1 = wienerIntegralKernel hB := by sorry
