-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinateNormalColumn_diff_le_ambient
-- name    : OAI.PiExponent.FormalInterpolation.coordinateNormalColumn_diff_le_ambient
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T00:43:48.699063+00:00
-- url     : https://prove2.me/theorems/ff0632d7-b04f-4921-b999-017e5d991bf0
-- title:
--   Upper bound for generic coordinate rank plus differential dimension
-- statement:
--   The generic coordinate Jacobian rank plus the function field’s differential dimension is at most the number of ambient coordinates. The conormal sequence provides a route by bounding the Jacobian rank by codimension.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.Extension.Cotangent.Basic

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.coordinateNormalColumn_diff_le_ambient
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    Module.finrank (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P)
      (Submodule.span (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P)
        (Set.range (OAI.PiExponent.FormalInterpolation.coordinateNormalColumnAtPrime P))) +
      Module.finrank (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P)
        (Ω[OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P⁄Complex]) ≤ m + 1 := by sorry
