-- Prove2me | Theorems.Thm_NumberField_exists_algHom_cyclotomicField_of_finrank_le_two
-- name    : NumberField.exists_algHom_cyclotomicField_of_finrank_le_two
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T02:21:27.979017+00:00
-- url     : https://prove2.me/theorems/492e868c-0ab8-4009-a6e0-79f90dbd6247
-- title:
--   Number fields of degree at most $2$ embed in cyclotomic fields
-- statement:
--   Let $\mathbb{K}$ be a number field with $[\mathbb{K}:\mathbb{Q}] \le 2$. Then there are an integer $n \ge 1$ and a homomorphism of $\mathbb{Q}$-algebras
--   $$\mathbb{K} \longrightarrow \mathbb{Q}(\zeta_n),$$
--   where $\zeta_n$ denotes a primitive $n$-th root of unity.
--
--   In other words, $\mathbb{Q}$ itself and every quadratic field $\mathbb{Q}(\sqrt d)$ are (isomorphic to) subfields of cyclotomic fields. This is the case $[\mathbb{K}:\mathbb{Q}] \le 2$ of the Kronecker–Weber theorem; every field of degree $\le 2$ is Galois over $\mathbb{Q}$ with abelian Galois group, so no Galois hypothesis is needed. Classically it is the statement that square roots of rational numbers lie in cyclotomic fields, the key instance being $\sqrt{(-1)^{(p-1)/2}\,p} \in \mathbb{Q}(\zeta_p)$ for an odd prime $p$.
--
--   **Formalization note.** $\mathbb{Q}(\zeta_n)$ is Mathlib's `CyclotomicField n ℚ`, and the embedding is an unspecified `K →ₐ[ℚ] CyclotomicField n ℚ` (automatically injective since $\mathbb{K}$ is a field). The hypothesis $[\mathbb{K}:\mathbb{Q}] \le 2$ is `Module.finrank ℚ K ≤ 2`; since $\mathbb{K}$ is a number field its degree is at least $1$.
-- source:
--   K. Ireland and M. Rosen, A Classical Introduction to Modern Number Theory, 2nd ed., GTM 84, Chapter 6, Proposition 6.3.2 (the quadratic Gauss sum satisfies g^2 = (-1)^{(p-1)/2} p), whence sqrt(+-p) lies in Q(zeta_p); together with sqrt(-1) = zeta_4 and sqrt(2) = zeta_8 + zeta_8^{-1} this gives the degree-2 case of the Kronecker-Weber theorem (L. C. Washington, Introduction to Cyclotomic Fields, 2nd ed., GTM 83, Theorem 14.1).

import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Basic

open Module

theorem NumberField.exists_algHom_cyclotomicField_of_finrank_le_two (K : Type*) [Field K]
    [NumberField K] (hK : finrank ℚ K ≤ 2) :
    ∃ n : ℕ, 0 < n ∧ Nonempty (K →ₐ[ℚ] CyclotomicField n ℚ) := by sorry
