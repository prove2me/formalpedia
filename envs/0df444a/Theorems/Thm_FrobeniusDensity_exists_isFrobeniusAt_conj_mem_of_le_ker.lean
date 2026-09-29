-- Prove2me | Theorems.Thm_FrobeniusDensity_exists_isFrobeniusAt_conj_mem_of_le_ker
-- name    : FrobeniusDensity.exists_isFrobeniusAt_conj_mem_of_le_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/6ca85171-b5c8-5ad9-9274-4569e5053148
-- title:
--   Chebotarev existence: every element is conjugate to a Frobenius
-- statement:
--   Let $F$ be a number field which is Galois over $\mathbb{Q}$ and which is endowed with an $F$-algebra structure on the fixed algebraic closure $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, and write $G = \overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$ for the group of $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}}$. Let $H$ be a subgroup of $G$ containing the kernel of the restriction homomorphism $G \to (F \simeq_{\mathbb{Q}} F)$ given by `AlgEquiv.restrictNormalHom`, let $S$ be a finite set of natural numbers, and let $\sigma \in G$. Then there exist a natural number $\ell$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, and elements $\tau, g \in G$ such that: $\ell$ is prime; $\ell \notin S$; $A$ lies over $\ell$ in the sense that the image of $\ell$ in $\overline{\mathbb{Q}}$ is a non-unit of $A$; $\tau$ is a Frobenius element at $A$ for $\ell$, that is, $\tau$ lies in the decomposition subgroup of $A$ over $\mathbb{Q}$ and the induced automorphism of the residue field of $A$ sends every $x$ to $x^{\ell}$; and $g\tau g^{-1}\sigma^{-1} \in H$. No density or counting assertion is made, and $\ell$ is not required to be unramified in $F$.
--
--   This is the existence half of the Chebotarev density theorem over $\mathbb{Q}$, packaged at the level of the absolute Galois group: since $H$ contains the kernel of restriction to $F$, it says that every element of $\mathrm{Gal}(F/\mathbb{Q})$ is the restriction of a conjugate of a Frobenius element at some prime outside a prescribed finite set. It is used throughout the Galois-theoretic parts of the argument, where a Frobenius element in a prescribed conjugacy class and avoiding the bad primes of a given representation is needed; its proof reduces the statement to the corresponding assertion for arithmetic Frobenius elements at maximal ideals of the ring of integers of a finite Galois extension, via [`NumberField.exists_prime_isArithFrobAt_of_isGalois`](thm.html#NumberField.exists_prime_isArithFrobAt_of_isGalois) and [`ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime`](thm.html#ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FrobeniusDensity_exists_isFrobeniusAt_conj_mem_of_le_ker.lean

import Mathlib
import Definitions.Def_GaloisRep_FrobeniusPowerDense

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem FrobeniusDensity.exists_isFrobeniusAt_conj_mem_of_le_ker (F : Type) [Field F] [NumberField F]
    [IsGalois ℚ F] [Algebra F (AlgebraicClosure ℚ)]
    {H : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)}
    (hker : (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker ≤ H)
    (S : Finset ℕ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ∃ (ℓ : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ))
      (τ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      ℓ.Prime ∧ ℓ ∉ S ∧ A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt τ ℓ ∧ g * τ * g⁻¹ * σ⁻¹ ∈ H := by sorry
