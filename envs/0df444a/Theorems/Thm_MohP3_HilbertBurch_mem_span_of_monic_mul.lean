-- Prove2me | Theorems.Thm_MohP3_HilbertBurch_mem_span_of_monic_mul
-- name    : MohP3.HilbertBurch.mem_span_of_monic_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:12:03.074398+00:00
-- url     : https://prove2.me/theorems/252f6994-7d8d-48f0-97fa-446fa04ee0d2
-- title:
--   Hilbert Burch: mem span of monic mul
-- statement:
--   If `t` is monic in `x` over `K[y,z]` and `h ∈ K[y,z]`, then `t` is a
--   nonzerodivisor on `K[x,y,z]/(h)`.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L270-L289
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HilbertBurch.lean#L270-L289

module
public import Definitions.Def_MohP3_Generic
public import Mathlib
public import Definitions.Def_MohP3_HilbertBurch
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open MohP3 MohP3.HilbertBurch
open Matrix
open MvPolynomial
variable {K : Type*} [CommRing K]

theorem MohP3.HilbertBurch.mem_span_of_monic_mul (h : MvPolynomial (Fin 2) K) (t u : MvPolynomial (Fin 3) K)
    (ht : (xEquiv t).Monic)
    (hu : t * u ∈ Ideal.span {xEquiv.symm (Polynomial.C h)}) :
    u ∈ Ideal.span {xEquiv.symm (Polynomial.C h)} := by sorry
