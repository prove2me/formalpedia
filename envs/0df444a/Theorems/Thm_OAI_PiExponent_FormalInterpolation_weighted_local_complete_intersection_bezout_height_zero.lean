-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_local_complete_intersection_bezout_height_zero
-- name    : OAI.PiExponent.FormalInterpolation.weighted_local_complete_intersection_bezout_height_zero
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T21:28:50.060299+00:00
-- url     : https://prove2.me/theorems/15343781-baf7-4e23-b81d-fccbc76f6962
-- title:
--   Weighted local Bézout bound in height zero
-- statement:
--   Prove the target in the zero-height case. The empty coordinate basis gives an empty product, and minimality at height zero reduces the local quotient length to one; the result then follows from the positive bound on H.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Definitions.Def_OAI_PiExponent_ComponentLocalLength
import Mathlib.RingTheory.Ideal.Height

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.weighted_local_complete_intersection_bezout_height_zero
    {m k : Nat} (w : Fin (m + 1) → Rat)
    (hw : ∀ i, 0 < (w i : Real)) (H : Real) (hH : 0 < H)
    (f : Fin k → MvPolynomial (Fin (m + 1)) Complex)
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]
    (hminimal : (Ideal.span (Set.range f)).IsMinimalPrime P)
    (hdegree : ∀ j, logarithmicDegreeBound w H (f j))
    (A : Finset (Fin (m + 1)))
    (hA : coordinateNormalBasisAtPrime P A)
    (hcard : A.card = P.height)
    (L : Nat)
    (hlength : componentLocalLength (Ideal.span (Set.range f)) P = (L : ENat))
    (hz : P.height = 0) :
    (L : Real) * (∏ i ∈ A, (w i : Real)) ≤ 2 * H ^ A.card := by sorry
