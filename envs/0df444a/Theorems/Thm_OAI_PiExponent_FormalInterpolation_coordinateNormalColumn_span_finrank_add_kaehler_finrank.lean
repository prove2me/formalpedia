-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinateNormalColumn_span_finrank_add_kaehler_finrank
-- name    : OAI.PiExponent.FormalInterpolation.coordinateNormalColumn_span_finrank_add_kaehler_finrank
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T00:34:35.274981+00:00
-- url     : https://prove2.me/theorems/533178b0-c697-415c-93d0-98dbb9c38cf0
-- title:
--   Generic coordinate Jacobian rank plus differential dimension
-- statement:
--   For the prime component's function field, the dimension of the span of the coordinate derivative columns plus the dimension of its module of Kähler differentials over ℂ equals the number of ambient coordinates.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.Extension.Cotangent.Basic

theorem OAI.PiExponent.FormalInterpolation.coordinateNormalColumn_span_finrank_add_kaehler_finrank
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    Module.finrank (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P)
      (Submodule.span (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P)
        (Set.range (OAI.PiExponent.FormalInterpolation.coordinateNormalColumnAtPrime P))) +
      Module.finrank (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P)
        (Ω[OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P⁄Complex]) = m + 1 := by sorry
