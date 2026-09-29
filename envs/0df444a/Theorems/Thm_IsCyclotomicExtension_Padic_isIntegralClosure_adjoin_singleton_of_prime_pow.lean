-- Prove2me | Theorems.Thm_IsCyclotomicExtension_Padic_isIntegralClosure_adjoin_singleton_of_prime_pow
-- name    : IsCyclotomicExtension.Padic.isIntegralClosure_adjoin_singleton_of_prime_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/37bd313e-c6cb-55b8-ad57-3174a9e8df11
-- title:
--   Ring of integers of ℚₚ(ζ_{p^k}) is ℤₚ[ζ]
-- statement:
--   Let $p$ be a prime and $k$ a natural number, and let $K$ be a field carrying algebra structures over $\mathbb{Q}_p$ and over $\mathbb{Z}_p$ which are compatible in the sense that $\mathbb{Z}_p \to \mathbb{Q}_p \to K$ is a scalar tower. Assume $K$ is a $p^k$-th cyclotomic extension of $\mathbb{Q}_p$, that is, $K$ contains a primitive $p^k$-th root of unity and is generated over $\mathbb{Q}_p$ by the roots of $X^{p^k} - 1$. Let $\zeta \in K$ be a primitive $p^k$-th root of unity. The conclusion is that the $\mathbb{Z}_p$-subalgebra $\mathbb{Z}_p[\zeta] =$ `Algebra.adjoin ℤ_[p] {ζ}` of $K$ is the integral closure of $\mathbb{Z}_p$ in $K$: the inclusion of $\mathbb{Z}_p[\zeta]$ into $K$ is injective, and an element of $K$ lies in its image exactly when it is integral over $\mathbb{Z}_p$. The degenerate case $k = 0$, where $p^k = 1$, $K = \mathbb{Q}_p$ and $\zeta = 1$, is included.
--
--   This is the local statement that the ring of integers of the $p^k$-th cyclotomic extension $\mathbb{Q}_p(\zeta_{p^k})$ of $\mathbb{Q}_p$ is the monogenic ring $\mathbb{Z}_p[\zeta_{p^k}]$, the analogue of the corresponding global fact for $\mathbb{Q}(\zeta_{p^k})$. It is used in the estimate [`PadicAlgCl.norm_apply_sub_le_norm_apply_sub_of_mem_cyclotomicTower`](thm.html#PadicAlgCl.norm_apply_sub_le_norm_apply_sub_of_mem_cyclotomicTower) comparing absolute values of differences of elements of the cyclotomic tower over $\mathbb{Q}_p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsCyclotomicExtension_Padic_isIntegralClosure_adjoin_singleton_of_prime_pow.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsCyclotomicExtension.Padic.isIntegralClosure_adjoin_singleton_of_prime_pow
    (p : ℕ) [Fact p.Prime] (k : ℕ) (K : Type*) [Field K] [Algebra ℚ_[p] K]
    [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K] [IsCyclotomicExtension {p ^ k} ℚ_[p] K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ (p ^ k)) :
    IsIntegralClosure (Algebra.adjoin ℤ_[p] ({ζ} : Set K)) ℤ_[p] K := by sorry
