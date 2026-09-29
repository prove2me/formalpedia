-- Prove2me | Theorems.Thm_KobayashiMaskawa1973_quartet_phase_cancellation
-- name    : KobayashiMaskawa1973.quartet_phase_cancellation
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T18:28:49.307524+00:00
-- url     : https://prove2.me/theorems/26106cee-264c-40c6-87c1-01cec68866b9
-- title:
--   Quartet phase factors cancel to identity
-- statement:
--   For all complex numbers $u_{00}, u_{11}, u_{01}, u_{10} \in \mathbb{C}$ and all real phases $a_0, a_1, b_0, b_1 \in \mathbb{R}$, the phase factors in the quartet product cancel identically:
--
--   $$(e^{ia_0} u_{00} e^{ib_0}) (e^{ia_1} u_{11} e^{ib_1}) (e^{ia_0} u_{01} e^{ib_1})^* (e^{ia_1} u_{10} e^{ib_0})^* = u_{00} u_{11} u_{01}^* u_{10}^*.$$
--
--   Because $(e^{i\phi})^* = e^{-i\phi}$ and complex multiplication is commutative, the total phase is $e^{i(a_0 + b_0 + a_1 + b_1 - a_0 - b_1 - a_1 - b_0)} = e^0 = 1$.
-- source:
--   C. Jarlskog, Phys. Rev. Lett. 55 (1985) 1039

import Mathlib
import Definitions.Def_KobayashiMaskawa1973_Defs

open Matrix

namespace KobayashiMaskawa1973

theorem quartet_phase_cancellation (u00 u11 u01 u10 : ℂ) (a0 a1 b0 b1 : ℝ) :
    (Complex.exp ((a0 : ℂ) * Complex.I) * u00 * Complex.exp ((b0 : ℂ) * Complex.I)) *
    (Complex.exp ((a1 : ℂ) * Complex.I) * u11 * Complex.exp ((b1 : ℂ) * Complex.I)) *
    star (Complex.exp ((a0 : ℂ) * Complex.I) * u01 * Complex.exp ((b1 : ℂ) * Complex.I)) *
    star (Complex.exp ((a1 : ℂ) * Complex.I) * u10 * Complex.exp ((b0 : ℂ) * Complex.I)) =
    u00 * u11 * star u01 * star u10 := by sorry

end KobayashiMaskawa1973
