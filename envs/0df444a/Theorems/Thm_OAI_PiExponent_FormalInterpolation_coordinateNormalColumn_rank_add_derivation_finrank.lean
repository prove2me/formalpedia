-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinateNormalColumn_rank_add_derivation_finrank
-- name    : OAI.PiExponent.FormalInterpolation.coordinateNormalColumn_rank_add_derivation_finrank
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T07:28:21.705416+00:00
-- url     : https://prove2.me/theorems/837fcdbe-7283-4512-80bb-a4db6cd1bce0
-- title:
--   Coordinate rank and function-field derivations
-- statement:
--   The coordinate-column span dimension plus the derivation dimension of the function field equals the number of coordinates. Use the linear map sending coordinate coefficients to the corresponding linear combination of columns. Its image is the displayed span, and its kernel consists of coordinate values defining a polynomial derivation that vanishes on P. Such a derivation descends to the quotient and extends to its fraction field; conversely, a derivation of that field is determined by its values on the polynomial coordinates. This reduces the claim to rank–nullity.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Ideal.Height

open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.coordinateNormalColumn_rank_add_derivation_finrank
    {m : Nat} (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    Module.finrank (logarithmicPrimeField P)
        (Submodule.span (logarithmicPrimeField P)
          (Set.range (coordinateNormalColumnAtPrime P))) +
      Module.finrank (logarithmicPrimeField P)
        (Derivation Complex (logarithmicPrimeField P) (logarithmicPrimeField P)) = m + 1 := by sorry
