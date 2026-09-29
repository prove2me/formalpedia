-- Prove2me | Theorems.Thm_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension
-- name    : NumberField.exists_prime_isArithFrobAt_of_isCyclotomicExtension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/88f81f33-ebb3-52ba-abbd-d68f3adf8f94
-- title:
--   Arithmetic Frobenius realising any automorphism of a cyclotomic extension
-- statement:
--   Let $K$ and $L$ be number fields with $L$ an algebra over $K$ such that $L/K$ is Galois, let $m$ be a nonzero natural number, and assume $L$ is a cyclotomic extension of $K$ for the set $\{m\}$, i.e. $L$ is generated over $K$ by the $m$-th roots of unity and contains a primitive $m$-th root of unity. Let $\tau$ be a $K$-algebra automorphism of $L$ and let $S$ be a finite set of natural numbers. Then there exist a rational prime $p \notin S$ and a maximal ideal $P$ of the ring of integers $\mathcal{O}_L$ with $p \in P$ such that $\tau$ is an arithmetic Frobenius at $P$ relative to $\mathbb{Z}$: for every $x \in \mathcal{O}_L$ one has $\tau(x) \equiv x^{\,N} \pmod P$, where $N = \#\bigl(\mathbb{Z}/(P \cap \mathbb{Z})\bigr)$. Since $p \in P$ and $P$ is maximal, this cardinality is $p$, so the congruence reads $\tau(x) \equiv x^{p} \pmod P$; in particular the residue characteristic can be chosen to avoid any prescribed finite set of integers.
--
--   This is the cyclotomic case of the existence of a prime with prescribed Frobenius, equivalently the form of Dirichlet's theorem on primes in arithmetic progressions over a number field: every element of $\operatorname{Gal}(K(\zeta_m)/K)$ occurs as an arithmetic Frobenius at a degree-one prime outside a given finite set. It is the input from which the corresponding statement for an arbitrary finite Galois extension of number fields, [`NumberField.exists_prime_isArithFrobAt_of_isGalois`](thm.html#NumberField.exists_prime_isArithFrobAt_of_isGalois), is deduced.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem NumberField.exists_prime_isArithFrobAt_of_isCyclotomicExtension
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L]
    (τ : L ≃ₐ[K] L) (S : Finset ℕ) :
    ∃ p : ℕ, p.Prime ∧ p ∉ S ∧ ∃ P : Ideal (𝓞 L), P.IsMaximal ∧ (p : 𝓞 L) ∈ P ∧
      IsArithFrobAt ℤ τ P := by sorry
