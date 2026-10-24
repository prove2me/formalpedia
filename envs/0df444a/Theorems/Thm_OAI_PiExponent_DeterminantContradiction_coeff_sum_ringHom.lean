-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_coeff_sum_ringHom
-- name    : OAI.PiExponent.DeterminantContradiction.coeff_sum_ringHom
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T07:49:48.452976+00:00
-- url     : https://prove2.me/theorems/64cf0a42-19e3-479c-b814-7413f7d4c458
-- title:
--   Coefficient extraction preserves finite sums after a polynomial map
-- statement:
--   For any finite family of multivariate polynomials and any polynomial ring homomorphism, extracting a fixed coefficient after mapping the sum gives the sum of the mapped coefficients.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.Algebra.MvPolynomial.Basic
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.coeff_sum_ringHom
    {α σ τ : Type*} [Fintype α] [DecidableEq σ] [DecidableEq τ]
    (φ : MvPolynomial σ Complex →+* MvPolynomial τ Complex)
    (e : τ →₀ Nat) (f : α → MvPolynomial σ Complex) :
    (φ (∑ x, f x)).coeff e = ∑ x, (φ (f x)).coeff e := by sorry
