-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_trdeg_coordinate_bound
-- name    : OAI.PiExponent.FormalInterpolation.trdeg_coordinate_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T00:25:34.354999+00:00
-- url     : https://prove2.me/theorems/ec386f99-aaf0-4508-af76-e1299105c59c
-- title:
--   Transcendence degree is bounded by the number of coordinates
-- statement:
--   The fraction field of a prime quotient of a polynomial ring in `m + 1` variables over ℂ has transcendence degree at most `m + 1`.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Extension.Cotangent.Basic

theorem OAI.PiExponent.FormalInterpolation.trdeg_coordinate_bound
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    (Algebra.trdeg Complex (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P)).toNat ≤ m + 1 := by sorry
