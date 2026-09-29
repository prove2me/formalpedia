-- Prove2me | Theorems.Thm_IsPrimitiveRoot_existsUnique_eq_pow_val
-- name    : IsPrimitiveRoot.existsUnique_eq_pow_val
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/381d8802-39ce-5c8a-abcb-6a8e80f75e13
-- title:
--   Discrete logarithm on μₚ: unique ℤ/p-valued exponents
-- statement:
--   Let $R$ be a commutative ring that is a domain, and let $\iota$ be an arbitrary index type. Let $\zeta$ be a unit of $R$ and $p$ a natural number with $p \neq 0$, and assume $\zeta$ is a primitive $p$-th root of unity in the group $R^\times$ (in the sense of Mathlib's `IsPrimitiveRoot`: $\zeta^p = 1$ and every $l$ with $\zeta^l = 1$ satisfies $p \mid l$). Let $f : \iota \to R^\times$ be a family of units with $f(i)^p = 1$ for every $i$. Then there is exactly one function $c : \iota \to \mathbb{Z}/p\mathbb{Z}$ such that $f(i) = \zeta^{\,\tilde{c}(i)}$ for all $i$, where $\tilde{c}(i) \in \{0, \dots, p-1\}$ denotes the canonical natural-number representative `ZMod.val` of $c(i)$. Uniqueness is asserted for the function $c$ itself, i.e. any two such exponent functions agree pointwise as elements of $\mathbb{Z}/p\mathbb{Z}$.
--
--   This is the discrete logarithm to the base $\zeta$ on the $p$-torsion of $R^\times$, packaged so that a family of $\mu_p$-valued data is replaced by a unique family of exponents in $\mathbb{Z}/p\mathbb{Z}$. It is used to translate between $\mu_p$-valued multiplicative cochains and $\mathbb{Z}/p$-valued additive ones, for instance in the construction of unipotent models of residual representations and in the cohomological computations for characters twisted by the cyclotomic character.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsPrimitiveRoot_existsUnique_eq_pow_val.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsPrimitiveRoot.existsUnique_eq_pow_val
    {R ι : Type*} [CommRing R] [IsDomain R] {ζ : Rˣ} {p : ℕ} [NeZero p] (hζ : IsPrimitiveRoot ζ p) (f : ι → Rˣ) (hf : ∀ i, f i ^ p = 1) :
    ∃! c : ι → ZMod p, ∀ i, f i = ζ ^ (c i).val := by sorry
