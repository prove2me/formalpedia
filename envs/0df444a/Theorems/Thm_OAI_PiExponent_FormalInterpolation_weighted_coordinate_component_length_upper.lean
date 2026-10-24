-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_coordinate_component_length_upper
-- name    : OAI.PiExponent.FormalInterpolation.weighted_coordinate_component_length_upper
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-24T04:40:00.10279+00:00
-- url     : https://prove2.me/theorems/8f29023d-9611-49e0-ad6d-3d7405f07d12
-- title:
--   Weighted Bézout upper bound for local component length
-- statement:
--   A minimal component of equations of weighted degree at most H has finite local quotient length L. For any coordinate normal basis A, L times the selected weight product is at most 2H^{|A|}. Prove by generic projection, finite free power substitution clearing rational weights, and isolated-intersection Bézout. If A is empty, the coordinate normal basis forces P to be zero; the local quotient has length one, consistent with the bound.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Definitions.Def_OAI_PiExponent_ComponentLocalLength

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.weighted_coordinate_component_length_upper
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
