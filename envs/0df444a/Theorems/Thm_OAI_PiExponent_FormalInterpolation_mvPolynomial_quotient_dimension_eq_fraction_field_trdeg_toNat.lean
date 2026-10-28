-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_mvPolynomial_quotient_dimension_eq_fraction_field_trdeg_toNat
-- name    : OAI.PiExponent.FormalInterpolation.mvPolynomial_quotient_dimension_eq_fraction_field_trdeg_toNat
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T07:09:51.230769+00:00
-- url     : https://prove2.me/theorems/54080e26-18ae-40b0-a4b7-7a4d9fe61932
-- title:
--   Quotient dimension equals fraction-field transcendence degree
-- statement:
--   For a prime ideal in a finite-variable polynomial ring over ℂ, the Krull dimension of the quotient equals the natural-number transcendence degree of its fraction field. The prime quotient is a finite-type domain over ℂ, so this is the affine-domain dimension theorem.

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

theorem OAI.PiExponent.FormalInterpolation.mvPolynomial_quotient_dimension_eq_fraction_field_trdeg_toNat
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    ringKrullDim (MvPolynomial (Fin (m + 1)) Complex ⧸ P) =
      (Algebra.trdeg Complex
        (FractionRing (MvPolynomial (Fin (m + 1)) Complex ⧸ P))).toNat := by sorry
