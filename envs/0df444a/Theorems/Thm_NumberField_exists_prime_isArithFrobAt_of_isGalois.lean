-- Prove2me | Theorems.Thm_NumberField_exists_prime_isArithFrobAt_of_isGalois
-- name    : NumberField.exists_prime_isArithFrobAt_of_isGalois
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/606b87ff-3296-5e01-821e-47b142c462ae
-- title:
--   Chebotarev existence: every Galois element is an arithmetic Frobenius
-- statement:
--   Let $K$ and $L$ be number fields with $L$ an extension of $K$ that is Galois, let $\sigma$ be a $K$-algebra automorphism of $L$, and let $S$ be a finite set of natural numbers. Then there is a natural number $p$ with the following properties: $p$ is prime, $p \notin S$, and there is an ideal $P$ of the ring of integers $\mathcal{O}_L$ such that $P$ is maximal, the image of $p$ in $\mathcal{O}_L$ lies in $P$, and $\sigma$ is an arithmetic Frobenius at $P$ relative to $\mathbb{Z}$ in the sense of `IsArithFrobAt ℤ σ P`, i.e. $\sigma(x) \equiv x^{q} \pmod{P}$ for every $x \in \mathcal{O}_L$, where $q$ is the cardinality of the residue field of $\mathbb{Z}$ at the prime $P \cap \mathbb{Z}$; since $p \in P$ and $P$ is maximal, $P \cap \mathbb{Z} = p\mathbb{Z}$ and the exponent is $q = p$. Thus every element of $\mathrm{Gal}(L/K)$ arises as an arithmetic Frobenius at some maximal ideal of $\mathcal{O}_L$ whose residue characteristic avoids any prescribed finite set of naturals; no unramifiedness assertion is made, and the prime below $P$ in $K$ is forced to have absolute residue degree one because $\sigma$ fixes $K$ pointwise.
--
--   This is the existence form of Chebotarev's density theorem for a finite Galois extension of number fields, with the extra freedom of avoiding finitely many residue characteristics. It feeds the project's Frobenius-density development, being cited by [`FrobeniusDensity.exists_isFrobeniusAt_conj_mem_of_le_ker`](thm.html#FrobeniusDensity.exists_isFrobeniusAt_conj_mem_of_le_ker), and is reduced here to the case of a cyclotomic extension via [`NumberField.exists_prime_isArithFrobAt_of_isCyclotomicExtension`](thm.html#NumberField.exists_prime_isArithFrobAt_of_isCyclotomicExtension).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem NumberField.exists_prime_isArithFrobAt_of_isGalois
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (σ : L ≃ₐ[K] L) (S : Finset ℕ) :
    ∃ p : ℕ, p.Prime ∧ p ∉ S ∧ ∃ P : Ideal (𝓞 L), P.IsMaximal ∧ (p : 𝓞 L) ∈ P ∧
      IsArithFrobAt ℤ σ P := by sorry
