-- Prove2me | Theorems.Thm_GaloisRep_sub_mul_log_le_tsum_rpow_neg_of_frobenius_mem_of_surjective
-- name    : GaloisRep.sub_mul_log_le_tsum_rpow_neg_of_frobenius_mem_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/6c581167-4960-51e5-a454-baa24aa5ffd9
-- title:
--   Chebotarev density for Gal(ℚ̄/ℚ), lower Dirichlet form
-- statement:
--   Let $Q$ be a finite group and let $\pi\colon\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)\to Q$ be a surjective group homomorphism, where the Galois group is that of the algebraic closure $\overline{\mathbb Q}$ of $\mathbb Q$, and assume [`GaloisFactorsThroughFiniteLevel`](def/GaloisRep_Residual.html#L17) for $\pi$, i.e. there is an intermediate field $L$ with $\mathbb Q\subseteq L\subseteq\overline{\mathbb Q}$ finite-dimensional over $\mathbb Q$ such that $\pi\sigma=1$ for every $\sigma$ fixing $L$ pointwise. Let $C\subseteq Q$ be a subset stable under conjugation, in the sense that $hgh^{-1}\in C$ whenever $g\in C$ and $h\in Q$, and let $\delta>0$. Then there is $s_0>1$ such that for every real $s$ with $1<s<s_0$,
--   $$\Bigl(\frac{|C|}{|Q|}-\delta\Bigr)\log\frac1{s-1}\;\le\;\sum_{p\in T}p^{-s},$$
--   where $|C|$ and $|Q|$ are the natural-number cardinalities of $C$ and $Q$, and $T$ is the set of primes $p$ such that: (i) for every valuation subring $A$ of $\overline{\mathbb Q}$ with $p$ a nonunit of $A$, $\pi$ kills the image in $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $A$ over $\mathbb Q$; and (ii) there are a valuation subring $A$ of $\overline{\mathbb Q}$ with $p$ a nonunit of $A$ and a $\sigma$ in the decomposition subgroup of $A$ over $\mathbb Q$ acting on the residue field of $A$ by $x\mapsto x^{p}$, with $\pi\sigma\in C$. The sum is the unconditional sum of $p^{-s}$ over the subtype of primes with these two properties.
--
--   This is Chebotarev's density theorem for the finite Galois extension of $\mathbb Q$ cut out by $\pi$, stated in Dirichlet-density form as a lower bound for a conjugation-stable subset $C$ of the quotient; applying it to the complement of $C$ recovers the density statement in full. It is used in the Deligne–Serre arguments of the project, namely in bounding the image of a residual representation by an upper-density hypothesis on Frobenius characteristic polynomials and in the irreducibility criterion for the attached matrix representation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_sub_mul_log_le_tsum_rpow_neg_of_frobenius_mem_of_surjective.lean

import Mathlib
import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem GaloisRep.sub_mul_log_le_tsum_rpow_neg_of_frobenius_mem_of_surjective
    {Q : Type} [Group Q] [Finite Q] (π : Γℚ →* Q) (hπ : Function.Surjective π)
    (hπc : GaloisFactorsThroughFiniteLevel π)
    (C : Set Q) (hC : ∀ g h : Q, g ∈ C → h * g * h⁻¹ ∈ C)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ s₀ : ℝ, 1 < s₀ ∧ ∀ s : ℝ, 1 < s → s < s₀ →
      ((Nat.card C : ℝ) / Nat.card Q - δ) * Real.log (1 / (s - 1)) ≤
        ∑' p : {p : ℕ // p.Prime ∧
            (∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
              ∀ σ ∈ A.inertiaSubgroupIn ℚ, π σ = 1) ∧
            ∃ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p ∧
              ∃ σ : Γℚ, A.IsFrobeniusAt σ p ∧ π σ ∈ C},
          ((p : ℕ) : ℝ) ^ (-s) := by sorry
