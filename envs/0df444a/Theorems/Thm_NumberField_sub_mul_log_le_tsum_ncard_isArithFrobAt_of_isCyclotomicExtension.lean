-- Prove2me | Theorems.Thm_NumberField_sub_mul_log_le_tsum_ncard_isArithFrobAt_of_isCyclotomicExtension
-- name    : NumberField.sub_mul_log_le_tsum_ncard_isArithFrobAt_of_isCyclotomicExtension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/887ea7f0-c3c4-53b7-9676-4713782119fc
-- title:
--   Dirichlet-density lower bound for Frobenius primes in K(ζ_m)/K
-- statement:
--   Let $K$ and $L$ be number fields with $L$ an algebra over $K$ such that $L/K$ is Galois, let $m$ be a nonzero natural number, and suppose $L$ is a cyclotomic extension of $K$ for the set $\{m\}$ (so $L$ is generated over $K$ by the $m$-th roots of unity, which are primitive and present in the required sense). Let $\sigma$ be a $K$-algebra automorphism of $L$ and let $\delta>0$ be a real number. Then there exists a real $s_0>1$ such that for every real $s$ with $1<s<s_0$,
--   $$\Bigl(\frac{1}{\operatorname{ord}(\sigma)}-\delta\Bigr)\,\log\frac{1}{s-1}\;\le\;\sum_{p}N_\sigma(p)\,p^{-s},$$
--   the sum being the unconditional infinite sum over all prime numbers $p$, and $N_\sigma(p)$ denoting the cardinality (as a natural number, via `Set.ncard`) of the set of maximal ideals $P$ of $\mathcal{O}_L$ such that the image of $p$ in $\mathcal{O}_L$ lies in $P$ and $\sigma$ is an arithmetic Frobenius element at $P$ relative to $\mathbb{Z}$, i.e. $\sigma(x)\equiv x^{q}\pmod P$ for all $x\in\mathcal{O}_L$, where $q$ is the cardinality of the residue field of the prime of $\mathbb{Z}$ below $P$. Here $\operatorname{ord}(\sigma)$ is the order of $\sigma$ in $\mathrm{Gal}(L/K)$.
--
--   This is the effective, Dirichlet-series form of Chebotarev's theorem for the cyclotomic extension $K(\zeta_m)/K$: the rational primes admitting a prime of $L$ at which $\sigma$ is the arithmetic Frobenius have lower Dirichlet density at least $1/\operatorname{ord}(\sigma)$. The proof combines the analytic estimate for the sum of $N(\mathfrak p)^{-s}$ over primes $\mathfrak p$ of $K$ whose absolute norm lies in a fixed class modulo $m$ with the bound [`FrobeniusDensity.tailSum_le`](thm.html#FrobeniusDensity.tailSum_le) on the contribution of primes of higher residue degree, and it is used by [`NumberField.sub_mul_log_le_tsum_ncard_isArithFrobAt`](thm.html#NumberField.sub_mul_log_le_tsum_ncard_isArithFrobAt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_sub_mul_log_le_tsum_ncard_isArithFrobAt_of_isCyclotomicExtension.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem NumberField.sub_mul_log_le_tsum_ncard_isArithFrobAt_of_isCyclotomicExtension
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L]
    (σ : L ≃ₐ[K] L) (δ : ℝ) (hδ : 0 < δ) :
    ∃ s₀ : ℝ, 1 < s₀ ∧ ∀ s : ℝ, 1 < s → s < s₀ →
      (1 / (orderOf σ : ℝ) - δ) * Real.log (1 / (s - 1)) ≤
        ∑' p : Nat.Primes, (({P : Ideal (𝓞 L) | P.IsMaximal ∧ ((p : ℕ) : 𝓞 L) ∈ P ∧
            IsArithFrobAt ℤ σ P}.ncard : ℕ) : ℝ) * ((p : ℕ) : ℝ) ^ (-s) := by sorry
