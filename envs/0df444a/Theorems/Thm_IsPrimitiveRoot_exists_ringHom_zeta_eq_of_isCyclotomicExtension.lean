-- Prove2me | Theorems.Thm_IsPrimitiveRoot_exists_ringHom_zeta_eq_of_isCyclotomicExtension
-- name    : IsPrimitiveRoot.exists_ringHom_zeta_eq_of_isCyclotomicExtension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/1aae61f9-879c-5cce-aec0-779ac9cba01e
-- title:
--   Embedding a cyclotomic extension of ℚ sending ζₙ to a given root
-- statement:
--   Let $n$ be a natural number that is nonzero, and let $K$ be a field equipped with a $\mathbb{Q}$-algebra structure which is a cyclotomic extension of $\mathbb{Q}$ for the singleton set $\{n\}$, so that $K$ contains a primitive $n$-th root of unity and is generated over $\mathbb{Q}$ by the $n$-th roots of unity. Let $L$ be a field of characteristic zero and let $\xi \in L$ be a primitive $n$-th root of unity, i.e. $\xi^n = 1$ and $\xi$ satisfies the universal property of `IsPrimitiveRoot` for $n$. Then there exists a ring homomorphism $\varphi : K \to L$ carrying the distinguished primitive $n$-th root of unity $\zeta =$ `IsCyclotomicExtension.zeta n ℚ K` of $K$ to $\xi$. Note that the conclusion asserts only the existence of a homomorphism of rings; that it is automatically a $\mathbb{Q}$-algebra map, and that it is injective, are not part of the statement.
--
--   This is the standard universal property of the $n$-th cyclotomic field: any field of characteristic zero containing a primitive $n$-th root of unity $\xi$ receives an embedding of $\mathbb{Q}(\zeta_n)$ with $\zeta_n \mapsto \xi$. It is used to transport cyclotomic constructions over $\mathbb{Q}(\zeta_n)$ — in particular rigid-analytic and Tate-curve presentations at full level — to an arbitrary coefficient field containing the required roots of unity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsPrimitiveRoot_exists_ringHom_zeta_eq_of_isCyclotomicExtension.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing Polynomial

theorem IsPrimitiveRoot.exists_ringHom_zeta_eq_of_isCyclotomicExtension
    (n : ℕ) [NeZero n] (K : Type*) [Field K] [Algebra ℚ K] [IsCyclotomicExtension {n} ℚ K]
    (L : Type*) [Field L] [CharZero L] (ξ : L) (hξ : IsPrimitiveRoot ξ n) :
    ∃ φ : K →+* L, φ (IsCyclotomicExtension.zeta n ℚ K) = ξ := by sorry
