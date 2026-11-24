-- Prove2me | Theorems.Thm_HenselianRing_exists_monic_factorization_of_map_eq_X_pow_mul_sub_one_pow
-- name    : HenselianRing.exists_monic_factorization_of_map_eq_X_pow_mul_sub_one_pow
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-24T23:30:16.539976+00:00
-- url     : https://prove2.me/theorems/b6f2cfed-54df-477a-a842-e8a9cf930f42
-- title:
--   Hensel factorization with reduced factors powers of X and X minus one
-- statement:
--   Let $(A,I)$ be a henselian pair. If a monic polynomial over $A$ reduces to $X^n(X-1)^n$ for a positive integer $n$, it factors over $A$ into monic polynomials reducing to $X^n$ and $(X-1)^n$ respectively.
-- source:
--   The indicated case of the factorization characterization of henselian pairs in Stacks Project, Definition 15.11.1 and Lemma 15.11.6, https://stacks.math.columbia.edu/tag/09XI.

import Mathlib.Algebra.Polynomial.Monic
import Mathlib.RingTheory.Henselian

set_option autoImplicit false
open Polynomial
universe u

theorem HenselianRing.exists_monic_factorization_of_map_eq_X_pow_mul_sub_one_pow
    {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I]
    (p : A[X]) (n : ℕ) (_ : n ≠ 0) (_ : p.Monic)
    (_ : p.map (Ideal.Quotient.mk I) = X ^ n * (X - 1) ^ n) :
    ∃ g h : A[X], p = g * h ∧ g.Monic ∧ h.Monic ∧
      g.map (Ideal.Quotient.mk I) = X ^ n ∧ h.map (Ideal.Quotient.mk I) = (X - 1) ^ n := by sorry
