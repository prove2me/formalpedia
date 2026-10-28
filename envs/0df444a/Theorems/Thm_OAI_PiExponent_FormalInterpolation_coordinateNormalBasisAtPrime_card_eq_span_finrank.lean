-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinateNormalBasisAtPrime_card_eq_span_finrank
-- name    : OAI.PiExponent.FormalInterpolation.coordinateNormalBasisAtPrime_card_eq_span_finrank
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T00:00:50.199145+00:00
-- url     : https://prove2.me/theorems/fb0ef592-5077-4ef7-80d5-fd3e8ee1419e
-- title:
--   Cardinality of a finite independent family equals its span dimension
-- statement:
--   The selected finite family’s cardinality equals the dimension of its span, using the linear independence included in `coordinateNormalBasisAtPrime`. This is a finite-dimensional linear algebra step, independent of the generic rank calculation.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.Ideal.Height

open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.coordinateNormalBasisAtPrime_card_eq_span_finrank
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]
    (A : Finset (Fin (m + 1)))
    (hA : coordinateNormalBasisAtPrime P A) :
    A.card = Module.finrank (logarithmicPrimeField P)
      (Submodule.span (logarithmicPrimeField P)
        (Set.range (fun i : A => coordinateNormalColumnAtPrime P i))) := by sorry
