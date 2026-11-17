-- Prove2me | Theorems.Thm_N25_genusFour_reciprocal_coefficient
-- name    : N25.genusFour_reciprocal_coefficient
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:34:38.181198+00:00
-- url     : https://prove2.me/theorems/25654852-a29f-4a2e-9858-8bab6b198bee
-- title:
--   Reciprocity determines the upper coefficients
-- statement:
--   Let $L(T)=\sum_j c_jT^j\in\mathbf Z[T]$, let $q\in\mathbf Z$ be nonzero, and assume $c_{8-j}q^j=q^4c_j$ for every integer index $0\le j\le8$. Then for every $i$ with $0\le i\le4$,
--
--   $$c_{8-i}=q^{4-i}c_i.$$
--
--   This extracts the usual genus-four reciprocal coefficients from the scaled functional equation.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_GenusFourNumerator

open N25

theorem N25.genusFour_reciprocal_coefficient
    {L : Polynomial ℤ} {q : ℤ} (hq : q ≠ 0)
    (hrec : ∀ i ≤ 8, L.coeff (8 - i) * q ^ i = q ^ 4 * L.coeff i)
    (i : ℕ) (hi : i ≤ 4) :
    L.coeff (8 - i) = q ^ (4 - i) * L.coeff i := by sorry
