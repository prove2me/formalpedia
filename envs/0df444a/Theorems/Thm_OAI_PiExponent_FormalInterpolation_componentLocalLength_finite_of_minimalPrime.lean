-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_componentLocalLength_finite_of_minimalPrime
-- name    : OAI.PiExponent.FormalInterpolation.componentLocalLength_finite_of_minimalPrime
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T20:55:14.844911+00:00
-- url     : https://prove2.me/theorems/b1a6554c-94fc-42ee-b2ee-618dd7d087a1
-- title:
--   Finite local component length at a minimal prime
-- statement:
--   The quotient by the generated ideal has finite length after localization at a minimal prime over that ideal. This child handles the existential finite-length part, independently of the weighted estimate.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Definitions.Def_OAI_PiExponent_ComponentLocalLength

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.componentLocalLength_finite_of_minimalPrime
    {m : Nat}
    (S : Finset (MvPolynomial (Fin (m + 1)) Complex))
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]
    (hminimal :
      (Ideal.span (↑S : Set (MvPolynomial (Fin (m + 1)) Complex))).IsMinimalPrime P) :
    ∃ L : Nat,
      componentLocalLength
        (Ideal.span (↑S : Set (MvPolynomial (Fin (m + 1)) Complex))) P =
          (L : ENat) := by sorry
