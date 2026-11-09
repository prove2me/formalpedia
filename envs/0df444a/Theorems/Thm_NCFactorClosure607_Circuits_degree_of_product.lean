-- Prove2me | Theorems.Thm_NCFactorClosure607_Circuits_degree_of_product
-- name    : NCFactorClosure607.Circuits.degree_of_product
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:15:30.446447+00:00
-- url     : https://prove2.me/theorems/523c2361-b617-4e28-8688-c8b0c8f834da
-- title:
--   Lemma 2.1: no zero divisors in $F\langle X\rangle$ and $\deg(PQ)=\deg P+\deg Q$
-- statement:
--   Let $F$ be a field and $X$ a set of noncommuting variables. For nonzero polynomials $P,Q\in F\langle X\rangle$,
--   $$PQ\neq0\qquad\text{and}\qquad\deg(PQ)=\deg P+\deg Q .$$
--
--   The degree additivity bounds the degrees of the cofactors of a factorization $f=agb$ by $\deg f$, which bounds the size of the cofactor data and of the extraction circuits.
--
--   Differences from the source:
--   - generalization: $X=\{x_1,\dots,x_m\}$ with $m\ge1$ → an arbitrary type `X`; reason: the statement for every type specializes to every finite nonempty variable set.
-- source:
--   V. Arvind, Pushkar S Joglekar, Factor Closure in Noncommutative Algebraic Complexity, STOC 2027 submission #607 (October 2026), p.5, Lemma 2.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/607.pdf

import Mathlib
import Definitions.Def_NCFactorClosure607_Circuits_Polynomials

namespace NCFactorClosure607.Circuits

/-- Lemma 2.1 (p.5): for nonzero noncommutative polynomials `P, Q ∈ F⟨X⟩`, `PQ ≠ 0` and
`deg(PQ) = deg P + deg Q`. -/
theorem degree_of_product {F : Type*} [Field F] {X : Type*} (P Q : FreeAlgebra F X)
    (hP : P ≠ 0) (hQ : Q ≠ 0) :
    P * Q ≠ 0 ∧ ncDeg (P * Q) = ncDeg P + ncDeg Q := by sorry

end NCFactorClosure607.Circuits
