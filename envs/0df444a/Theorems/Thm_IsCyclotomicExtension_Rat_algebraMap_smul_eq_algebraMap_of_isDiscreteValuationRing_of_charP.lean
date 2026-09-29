-- Prove2me | Theorems.Thm_IsCyclotomicExtension_Rat_algebraMap_smul_eq_algebraMap_of_isDiscreteValuationRing_of_charP
-- name    : IsCyclotomicExtension.Rat.algebraMap_smul_eq_algebraMap_of_isDiscreteValuationRing_of_charP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/752e038d-5720-5eb7-987f-7e8c96b400fb
-- title:
--   Inertia acts trivially on residue fields of ℚ(ζₚ)
-- statement:
--   Let $p$ be a prime and let $L$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of type $\{p\}$, i.e. $L$ is generated over $\mathbb{Q}$ by a primitive $p$-th root of unity. Let $A$ be a domain which is a discrete valuation ring, equipped with an algebra structure over which $L$ is the fraction field of $A$, and assume that the image of $p$ in $A$ lies in the maximal ideal of the local ring $A$. Let $k$ be a field of characteristic $p$ together with an $A$-algebra structure, so that $A \to k$ is a ring homomorphism killing $p$. Suppose the group $L \simeq_{\mathbb{Q}} L$ of $\mathbb{Q}$-algebra automorphisms of $L$ acts on $A$ by ring automorphisms (a multiplicative semiring action), and that this action is compatible with the inclusion $A \subseteq L$ in the sense that $\mathrm{algebraMap}_{A,L}(s \cdot a) = s(\mathrm{algebraMap}_{A,L}(a))$ for all automorphisms $s$ and all $a \in A$. Then for every such $s$ and every $a \in A$ the images of $s \cdot a$ and of $a$ in $k$ coincide: $\mathrm{algebraMap}_{A,k}(s \cdot a) = \mathrm{algebraMap}_{A,k}(a)$.
--
--   This is the statement that $p$ is totally ramified in $\mathbb{Q}(\zeta_p)$, so that the full group $\mathrm{Gal}(\mathbb{Q}(\zeta_p)/\mathbb{Q})$ is the inertia group at the prime above $p$ and therefore acts trivially on any residue field of characteristic $p$. It is used in the study of the special fibre of $X_1(Mp)$, where a Galois twist of a model over a discrete valuation ring with fraction field $\mathbb{Q}(\zeta_p)$ must be identified with the original one after reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsCyclotomicExtension_Rat_algebraMap_smul_eq_algebraMap_of_isDiscreteValuationRing_of_charP.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsCyclotomicExtension.Rat.algebraMap_smul_eq_algebraMap_of_isDiscreteValuationRing_of_charP
    (p : ℕ) [Fact p.Prime] (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A)
    (k : Type) [Field k] [CharP k p] [Algebra A k]
    [MulSemiringAction (L ≃ₐ[ℚ] L) A]
    (hΓA : ∀ (s : L ≃ₐ[ℚ] L) (a : A), algebraMap A L (s • a) = s (algebraMap A L a)) :
    ∀ (s : L ≃ₐ[ℚ] L) (a : A), algebraMap A k (s • a) = algebraMap A k a := by sorry
