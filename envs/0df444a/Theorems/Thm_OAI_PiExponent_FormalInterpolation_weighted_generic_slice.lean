-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_generic_slice
-- name    : OAI.PiExponent.FormalInterpolation.weighted_generic_slice
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T21:27:57.999921+00:00
-- url     : https://prove2.me/theorems/6f6ad612-0c80-41cc-8e9c-4ca39abb0e17
-- title:
--   Choose bounded equations cutting out a minimal component
-- statement:
--   Choose a family of as many bounded equations as the height of `P`, each in the original ideal, such that `P` is minimal over the ideal they generate.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.Ideal.Height

open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.weighted_generic_slice
    {m : Nat} (w : Fin (m + 1) → Rat)
    (hw : ∀ i, 0 < (w i : Real)) (H : Real) (hH : 0 < H)
    (S : Finset (MvPolynomial (Fin (m + 1)) Complex))
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]
    (hminimal :
      (Ideal.span (↑S : Set (MvPolynomial (Fin (m + 1)) Complex))).IsMinimalPrime P)
    (hdegree : ∀ g ∈ S, logarithmicDegreeBound w H g)
    (A : Finset (Fin (m + 1))) (hcard : A.card = P.height) :
    ∃ f : Fin A.card → MvPolynomial (Fin (m + 1)) Complex,
      (∀ j, f j ∈ Ideal.span (↑S : Set (MvPolynomial (Fin (m + 1)) Complex))) ∧
      (∀ j, logarithmicDegreeBound w H (f j)) ∧
      (Ideal.span (Set.range f)).IsMinimalPrime P := by sorry
