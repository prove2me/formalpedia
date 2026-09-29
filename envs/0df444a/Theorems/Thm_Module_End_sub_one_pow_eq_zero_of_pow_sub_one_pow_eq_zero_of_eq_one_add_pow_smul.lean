-- Prove2me | Theorems.Thm_Module_End_sub_one_pow_eq_zero_of_pow_sub_one_pow_eq_zero_of_eq_one_add_pow_smul
-- name    : Module.End.sub_one_pow_eq_zero_of_pow_sub_one_pow_eq_zero_of_eq_one_add_pow_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/d5588e4a-8713-5bba-a4d8-b3bac2637d01
-- title:
--   Minkowski–Serre rigidity modulo ℓᵃ≥ 3
-- statement:
--   Let $R$ be a commutative ring and $M$ an $R$-module (an additive commutative group with an $R$-module structure). Let $\ell$ be a prime number and $a$ a natural number with $\ell^a \ge 3$. Assume two conditions on $M$ relative to the image of $\ell$ in $R$: multiplication by $\ell$ is injective, i.e. $(\ell : R) \cdot x = 0$ forces $x = 0$; and $M$ is $\ell$-adically separated, i.e. any $x \in M$ that for every $k$ admits some $z \in M$ with $(\ell : R)^k \cdot z = x$ is zero. Let $m$ be a positive natural number such that every prime $r$ dividing $m$ with $r \ne \ell$ has unit image in $R$. Let $g, y$ be $R$-linear endomorphisms of $M$ with $g = 1 + (\ell : R)^a \cdot y$, so that $g$ is congruent to the identity modulo $\ell^a \operatorname{End}_R(M)$. Then for every natural number $n$, if $(g^m - 1)^n = 0$ in $\operatorname{End}_R(M)$, then $(g - 1)^n = 0$.
--
--   This is the algebraic rigidity statement, going back to Minkowski and in this form to Serre, that for $\ell^a \ge 3$ the kernel of the reduction $\operatorname{Aut}_R(M) \to \operatorname{Aut}(M/\ell^a M)$ contains no element whose $m$-th power is unipotent of a given exponent without the element itself being so; taking $n = 1$ and $g^m = 1$ recovers the absence of non-trivial torsion in that kernel. It is used here in the form [`TateModule.sub_one_pow_rep_eq_zero_of_pow_sub_one_pow_eq_zero_of_forall_torsionBy_smul_eq`](thm.html#TateModule.sub_one_pow_rep_eq_zero_of_pow_sub_one_pow_eq_zero_of_forall_torsionBy_smul_eq), where $M$ is an $\ell$-adic Tate module and $g$ the image of a group element under an $\ell$-adic representation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_End_sub_one_pow_eq_zero_of_pow_sub_one_pow_eq_zero_of_eq_one_add_pow_smul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Module.End.sub_one_pow_eq_zero_of_pow_sub_one_pow_eq_zero_of_eq_one_add_pow_smul
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {ℓ : ℕ} (hℓ : ℓ.Prime) {a : ℕ} (ha : 3 ≤ ℓ ^ a)
    (htf : ∀ x : M, (ℓ : R) • x = 0 → x = 0)
    (hsep : ∀ x : M, (∀ k : ℕ, ∃ z : M, (ℓ : R) ^ k • z = x) → x = 0)
    {m : ℕ} (hm : 0 < m) (hunit : ∀ r : ℕ, r.Prime → r ∣ m → r ≠ ℓ → IsUnit (r : R))
    (g y : Module.End R M) (hg : g = 1 + ((ℓ : R) ^ a) • y)
    {n : ℕ} (hn : (g ^ m - 1) ^ n = 0) : (g - 1) ^ n = 0 := by sorry
