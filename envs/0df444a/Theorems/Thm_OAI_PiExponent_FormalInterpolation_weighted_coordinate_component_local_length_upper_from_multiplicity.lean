-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_coordinate_component_local_length_upper_from_multiplicity
-- name    : OAI.PiExponent.FormalInterpolation.weighted_coordinate_component_local_length_upper_from_multiplicity
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-24T20:36:34.730064+00:00
-- url     : https://prove2.me/theorems/5d4b1cad-d099-4d44-a1a3-467e8e7e310e
-- title:
--   Weighted Bézout upper bound for the coordinate local length
-- statement:
--   The minimal-prime and coordinate normal-basis hypotheses give a finite local component length, bounded by the weighted Bézout quantity. This isolates the coordinate-slice, generic codimension, and weighted isolated-intersection estimate from the parent. The manuscript supplies the route: take a smooth generic point, slice transversely in the selected coordinates, then use weighted Bézout. For A empty, the local length is one and the stated right side is 2.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Definitions.Def_OAI_PiExponent_ComponentLocalLength

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.weighted_coordinate_component_local_length_upper_from_multiplicity
    {m : Nat} (w : Fin (m + 1) → Rat)
    (hw : ∀ i, 0 < (w i : Real)) (H : Real) (hH : 0 < H)
    (S : Finset (MvPolynomial (Fin (m + 1)) Complex))
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]
    (hminimal :
      (Ideal.span (↑S : Set (MvPolynomial (Fin (m + 1)) Complex))).IsMinimalPrime P)
    (hdegree : ∀ f ∈ S, logarithmicDegreeBound w H f)
    (A : Finset (Fin (m + 1)))
    (hA : coordinateNormalBasisAtPrime P A) :
    ∃ L : Nat,
      componentLocalLength
          (Ideal.span (↑S : Set (MvPolynomial (Fin (m + 1)) Complex))) P =
        (L : ENat) ∧
      (L : Real) * (∏ i ∈ A, (w i : Real)) ≤ 2 * H ^ A.card := by
  sorry
