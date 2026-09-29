-- Prove2me | Theorems.Thm_NumberField_sub_mul_log_le_tsum_ncard_isArithFrobAt
-- name    : NumberField.sub_mul_log_le_tsum_ncard_isArithFrobAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/24220bf8-5dd1-5b87-96a8-c13b58164931
-- title:
--   Chebotarev lower bound for arithmetic Frobenius, Dirichlet form
-- statement:
--   Let $L$ be a number field (a field of characteristic zero, finite-dimensional over $\mathbb{Q}$), let $\sigma$ be an automorphism of $L$ fixing $\mathbb{Q}$, i.e. an element of $L \simeq_{\text{alg}[\mathbb{Q}]} L$, and let $\delta$ be a positive real number; no hypothesis that $L/\mathbb{Q}$ be Galois is imposed. For a rational prime $p$, consider the set of ideals $P$ of the ring of integers $\mathcal{O}_L$ that are maximal, contain the image of $p$, and satisfy the predicate `IsArithFrobAt ℤ σ P`, i.e. $\sigma$ is an arithmetic Frobenius at $P$ over $\mathbb{Z}$: $\sigma$ induces on $\mathcal{O}_L/P$ the $q$-power map, where $q$ is the cardinality of the residue field of the prime of $\mathbb{Z}$ below $P$, so here $q = p$. Write $N_\sigma(p)$ for the cardinality (`Set.ncard`) of that set. The assertion is that there exists a real $s_0 > 1$ such that for every real $s$ with $1 < s < s_0$,
--   $$\Bigl(\tfrac{1}{\operatorname{ord}(\sigma)} - \delta\Bigr)\,\log\frac{1}{s-1} \;\le\; \sum_{p}' N_\sigma(p)\, p^{-s},$$
--   the sum being taken over all rational primes, with $\operatorname{ord}(\sigma)$ the order of $\sigma$ as a group element.
--
--   This is the cyclic case of Chebotarev's density theorem in lower Dirichlet-density form: the primes of $L$ at which a given $\mathbb{Q}$-automorphism $\sigma$ of $L$ is an arithmetic Frobenius have lower Dirichlet density at least $1/\operatorname{ord}(\sigma)$. It is obtained from the corresponding statement for a cyclotomic extension of a base field, and is used in [`GaloisRep.sub_mul_log_le_tsum_rpow_neg_of_frobenius_mem_of_surjective`](thm.html#GaloisRep.sub_mul_log_le_tsum_rpow_neg_of_frobenius_mem_of_surjective) to produce, for a Galois representation, sufficiently many primes whose Frobenius lies in a prescribed class.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_sub_mul_log_le_tsum_ncard_isArithFrobAt.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem NumberField.sub_mul_log_le_tsum_ncard_isArithFrobAt
    (L : Type) [Field L] [NumberField L] (σ : L ≃ₐ[ℚ] L) (δ : ℝ) (hδ : 0 < δ) :
    ∃ s₀ : ℝ, 1 < s₀ ∧ ∀ s : ℝ, 1 < s → s < s₀ →
      (1 / (orderOf σ : ℝ) - δ) * Real.log (1 / (s - 1)) ≤
        ∑' p : Nat.Primes, (({P : Ideal (𝓞 L) | P.IsMaximal ∧ ((p : ℕ) : 𝓞 L) ∈ P ∧
            IsArithFrobAt ℤ σ P}.ncard : ℕ) : ℝ) * ((p : ℕ) : ℝ) ^ (-s) := by sorry
