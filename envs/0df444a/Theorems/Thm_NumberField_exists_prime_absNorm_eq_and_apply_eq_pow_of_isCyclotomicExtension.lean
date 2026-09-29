-- Prove2me | Theorems.Thm_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension
-- name    : NumberField.exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/fd0131da-c0b4-549d-a13e-02d4ccf6ff12
-- title:
--   Primes of absolute degree one realising a cyclotomic automorphism
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $m$ be a natural number with $m \neq 0$, and suppose $L$ is an $m$-th cyclotomic extension of $K$ in the sense of Mathlib's `IsCyclotomicExtension {m} K L`. Let $\zeta \in L$ be a primitive $m$-th root of unity, let $\tau$ be a $K$-algebra automorphism of $L$, and let $S$ be a finite set of natural numbers. The assertion is that there exists a rational prime $p$ with $p \notin S$ together with an ideal $v$ of the ring of integers $\mathcal{O}_K$ such that $v$ is maximal, the absolute ideal norm $\mathrm{N}v = \#(\mathcal{O}_K/v)$ equals $p$, and $\tau(\zeta) = \zeta^{p}$. Thus $v$ is a prime of $K$ whose residue field is $\mathbb{F}_p$, i.e. a prime of absolute residue degree one lying over $p$, and raising to the $p$-th power on the $m$-th roots of unity reproduces the action of $\tau$. Since $S$ is arbitrary, infinitely many such primes $p$ occur.
--
--   This is the form in which Hecke's generalisation of Dirichlet's theorem on primes in arithmetic progressions is used here: each element of $\mathrm{Gal}(K(\zeta_m)/K)$, viewed inside $(\mathbb{Z}/m\mathbb{Z})^\times$, is the residue class of the absolute norm of a degree-one prime of $K$ outside any prescribed finite set of rational primes. It feeds [`NumberField.exists_prime_isArithFrobAt_of_isCyclotomicExtension`](thm.html#NumberField.exists_prime_isArithFrobAt_of_isCyclotomicExtension), which converts this into the existence of primes with prescribed arithmetic Frobenius.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem NumberField.exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] {ζ : L} (hζ : IsPrimitiveRoot ζ m)
    (τ : L ≃ₐ[K] L) (S : Finset ℕ) :
    ∃ p : ℕ, p.Prime ∧ p ∉ S ∧
      ∃ v : Ideal (𝓞 K), v.IsMaximal ∧ Ideal.absNorm v = p ∧ τ ζ = ζ ^ p := by sorry
