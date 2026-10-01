-- Prove2me | Theorems.Thm_LiouvilleDiffAlg_ratFunc_deriv_poly
-- name    : LiouvilleDiffAlg.ratFunc_deriv_poly
-- status  : Proved
-- author  : @vebis
-- created : 2026-10-01T11:41:10.072147+00:00
-- url     : https://prove2.me/theorems/62eaef4c-5cca-45ff-8b58-60d9ef03c8f1
-- title:
--   Derivative of a polynomial in K(X)
-- statement:
--   Assume $K$ is a field of characteristic zero with a derivation $D$, and $K(X)$ is the field of rational functions in one variable over $K$, equipped with a derivation (also written $D$) that extends the derivation of $K$. Suppose $DX=w$ for a polynomial $w\in K[X]$. Then for every polynomial $r\in K[X]$,
--
--   $$D r = r^{D} + w\,\frac{dr}{dX},$$
--
--   where $r^{D}\in K[X]$ denotes the polynomial obtained by applying $D$ to the coefficients of $r$ and $dr/dX$ is the formal derivative. In particular the derivative of a polynomial is again a polynomial.
--
--   This is the chain-rule formula that reduces differentiation in $K(X)$ to polynomial arithmetic.
--
--   **Formalization Note** The right-hand side is `Differential.implicitDeriv w r`.
-- source:
--   Rosenlicht, Integration in finite terms, Amer. Math. Monthly 79 (1972), 963–972 (proof of Liouville's theorem by induction on an elementary tower); Geddes–Czapor–Labahn, Algorithms for Computer Algebra (Kluwer, 1992), §12.4; Wikipedia, "Liouville's theorem (differential algebra)", oldid=1349223559, section "Basic theorem"

import Mathlib

open scoped Differential
open Polynomial

namespace LiouvilleDiffAlg

theorem ratFunc_deriv_poly {K : Type*} [Field K] [Differential K] [CharZero K]
    [Differential (RatFunc K)] [DifferentialAlgebra K (RatFunc K)]
    (w : K[X]) (hX : (RatFunc.X : RatFunc K)′ = algebraMap K[X] (RatFunc K) w) (r : K[X]) :
    (algebraMap K[X] (RatFunc K) r)′ = algebraMap K[X] (RatFunc K) (Differential.implicitDeriv w r) := by sorry

end LiouvilleDiffAlg
