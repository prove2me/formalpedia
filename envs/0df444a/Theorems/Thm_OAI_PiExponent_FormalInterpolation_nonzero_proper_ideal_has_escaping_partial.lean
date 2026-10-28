-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_nonzero_proper_ideal_has_escaping_partial
-- name    : OAI.PiExponent.FormalInterpolation.nonzero_proper_ideal_has_escaping_partial
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T04:32:54.484997+00:00
-- url     : https://prove2.me/theorems/a77ed5b6-84e1-4130-8109-6bc94110d4e3
-- title:
--   A nonzero proper characteristic-zero polynomial ideal has an escaping partial derivative
-- statement:
--   This supplies a nonzero generic normal column without assuming exclusion. Choose a nonzero element F of I of minimal total degree. Properness excludes nonzero constants. A nonconstant monomial with nonzero coefficient has a positive exponent; characteristic zero and `MvPolynomial.coeff_pderiv` then give a nonzero partial derivative. Every monomial of that derivative has strictly smaller total degree, so minimality excludes its membership in I. The inspected `MvPolynomial.totalDegree_eq_zero_iff_eq_C` handles the constant boundary. The argument works for arbitrary variable types because each polynomial has finite support; for an empty variable type, the nonzero-proper hypotheses are inconsistent. The reduction applies this lemma to P and proves that the kernel of the map into its fraction field is exactly P.

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.RingTheory.Ideal.Basic

theorem OAI.PiExponent.FormalInterpolation.nonzero_proper_ideal_has_escaping_partial
    {k σ : Type*} [Field k] [CharZero k]
    (I : Ideal (MvPolynomial σ k)) (hIbot : I ≠ ⊥) (hItop : I ≠ ⊤) :
    ∃ F : MvPolynomial σ k, F ∈ I ∧
      ∃ i : σ, MvPolynomial.pderiv i F ∉ I := by
  sorry
