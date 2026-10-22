-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_pderiv_support_lift
-- name    : OAI.PiExponent.FormalInterpolation.pderiv_support_lift
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-21T09:45:11.483924+00:00
-- url     : https://prove2.me/theorems/dd40c55e-59e5-4f17-85fe-a011dfb775ae
-- title:
--   Support exponents lift through a partial derivative
-- statement:
--   Every exponent supported by a partial derivative is obtained by lowering the differentiated coordinate of some exponent in the original polynomial by one; equivalently, adding one to that coordinate recovers an exponent in the original support.

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact

open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.pderiv_support_lift
    {d : Nat} (i : Fin d) (F : MvPolynomial (Fin d) Complex)
    (a : Fin d →₀ Nat) (ha : a ∈ (MvPolynomial.pderiv i F).support) :
    ∃ b ∈ F.support, b = a + Finsupp.single i 1 := by sorry
