-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_ambient_le_coordinateNormalColumn_diff
-- name    : OAI.PiExponent.FormalInterpolation.ambient_le_coordinateNormalColumn_diff
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T00:44:05.543643+00:00
-- url     : https://prove2.me/theorems/7bd85a39-bab5-46e5-a8cf-7b8e808927ab
-- title:
--   Lower bound for generic coordinate rank plus differential dimension
-- statement:
--   The ambient dimension is at most the sum of the generic coordinate Jacobian rank and the function field’s differential dimension. A proof route is the characteristic-zero generic Jacobian criterion together with the transcendence-degree formula for differentials.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.Extension.Cotangent.Basic

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.ambient_le_coordinateNormalColumn_diff
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    m + 1 ≤
      Module.finrank (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P)
        (Submodule.span (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P)
          (Set.range (OAI.PiExponent.FormalInterpolation.coordinateNormalColumnAtPrime P))) +
      Module.finrank (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P)
        (Ω[OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P⁄Complex]) := by sorry
