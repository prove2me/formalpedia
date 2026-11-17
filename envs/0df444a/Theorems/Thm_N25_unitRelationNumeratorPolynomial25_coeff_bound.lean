-- Prove2me | Theorems.Thm_N25_unitRelationNumeratorPolynomial25_coeff_bound
-- name    : N25.unitRelationNumeratorPolynomial25_coeff_bound
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:56:27.490564+00:00
-- url     : https://prove2.me/theorems/2dfd21de-3342-48c7-a81b-1d4cfe4b3651
-- title:
--   Every relevant numerator coefficient is smaller than $2^{360}$
-- statement:
--   Let $P_{199}(X)$ be the truncated unit-relation numerator polynomial. For every $n<4951$, $$|[X^n]P_{199}(X)|<2^{360}.$$ This bound allows four coprime modular evaluations to certify that each coefficient is zero.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_UnitRelationCertificate

set_option autoImplicit false
open N25
open Polynomial

theorem N25.unitRelationNumeratorPolynomial25_coeff_bound (n : ℕ) (hn : n < 4951) :
    |(unitRelationNumeratorPolynomial25 199).coeff n| < (2 : ℤ) ^ 360 := by sorry
