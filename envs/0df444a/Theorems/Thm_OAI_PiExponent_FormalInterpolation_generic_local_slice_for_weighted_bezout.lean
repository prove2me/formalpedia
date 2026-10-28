-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_generic_local_slice_for_weighted_bezout
-- name    : OAI.PiExponent.FormalInterpolation.generic_local_slice_for_weighted_bezout
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T21:23:09.094135+00:00
-- url     : https://prove2.me/theorems/c6d1b6a0-e7b6-4c24-976a-486f29cf318f
-- title:
--   Reduce a minimal component to a local complete intersection
-- statement:
--   For a minimal prime of a finitely generated ideal, choose as many generic linear combinations as the prime’s height. They remain in the original ideal, retain the weighted degree bound, make the prime minimal over the sliced ideal, and have finite local length at least that of the original quotient. The length comparison follows from the quotient map induced by containment; generic slicing supplies the minimal component.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Definitions.Def_OAI_PiExponent_ComponentLocalLength
import Mathlib.RingTheory.Ideal.Height

open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.generic_local_slice_for_weighted_bezout
    {m : Nat} (w : Fin (m + 1) → Rat)
    (hw : ∀ i, 0 < (w i : Real)) (H : Real) (hH : 0 < H)
    (S : Finset (MvPolynomial (Fin (m + 1)) Complex))
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]
    (hminimal :
      (Ideal.span (↑S : Set (MvPolynomial (Fin (m + 1)) Complex))).IsMinimalPrime P)
    (hdegree : ∀ g ∈ S, logarithmicDegreeBound w H g)
    (A : Finset (Fin (m + 1))) (hcard : A.card = P.height)
    (L : Nat)
    (hlength :
      componentLocalLength
        (Ideal.span (↑S : Set (MvPolynomial (Fin (m + 1)) Complex))) P =
          (L : ENat)) :
    ∃ f : Fin A.card → MvPolynomial (Fin (m + 1)) Complex,
      (∀ j, f j ∈ Ideal.span (↑S : Set (MvPolynomial (Fin (m + 1)) Complex))) ∧
      (∀ j, logarithmicDegreeBound w H (f j)) ∧
      (Ideal.span (Set.range f)).IsMinimalPrime P ∧
      ∃ M : Nat,
        componentLocalLength (Ideal.span (Set.range f)) P = (M : ENat) ∧
        L ≤ M := by sorry
