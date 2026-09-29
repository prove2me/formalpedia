-- Prove2me | Theorems.Thm_IsLocalRing_residueMap_comp_algHom_eq_of_surjective
-- name    : IsLocalRing.residueMap_comp_algHom_eq_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/df91dcd5-a8f8-54c5-b98b-539a3ecc7a60
-- title:
--   Residue compatibility of Λ-algebra maps out of a local ring
-- statement:
--   Let $\Lambda$ be a commutative ring, $k$ a field, and $\mathrm{res}_0 : \Lambda \to k$ a surjective ring homomorphism. Let $A$ be a commutative local ring that is a $\Lambda$-algebra, equipped with a ring homomorphism $r_A : A \to k$ whose kernel is exactly the maximal ideal of $A$ and which satisfies $r_A(\lambda \cdot 1_A) = \mathrm{res}_0(\lambda)$ for every $\lambda \in \Lambda$ (that is, $r_A$ lies over $\mathrm{res}_0$ along the structure map $\Lambda \to A$). Let $B$ be a commutative $\Lambda$-algebra, not assumed local, with a ring homomorphism $r_B : B \to k$ likewise satisfying $r_B(\lambda \cdot 1_B) = \mathrm{res}_0(\lambda)$ for all $\lambda \in \Lambda$. Then for every $\Lambda$-algebra homomorphism $\Phi : A \to B$ and every $a \in A$ one has $r_B(\Phi(a)) = r_A(a)$; in other words $r_B \circ \Phi = r_A$, so the residue compatibility of $\Phi$ is automatic rather than an extra condition.
--
--   This is the standard observation that, for test algebras whose map to the residue field $k$ is induced from $\Lambda$, compatibility with the residue maps need not be imposed on morphisms. It is used in the functor-of-points descriptions of deformation-type rings, where point sets are defined without the condition $r_B \circ \Phi = r_A$ and this condition is recovered afterwards; it is cited in the construction of algebra homomorphisms attached to level structures on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_residueMap_comp_algHom_eq_of_surjective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem IsLocalRing.residueMap_comp_algHom_eq_of_surjective
    (Λ : Type) [CommRing Λ] (k : Type) [Field k] (res₀ : Λ →+* k) (hres₀ : Function.Surjective res₀)
    (A : Type) [CommRing A] [IsLocalRing A] [Algebra Λ A]
    (rA : A →+* k) (hkerA : RingHom.ker rA = maximalIdeal A) (hrA : ∀ w : Λ, rA (algebraMap Λ A w) = res₀ w)
    (B : Type) [CommRing B] [Algebra Λ B] (rB : B →+* k) (hrB : ∀ w : Λ, rB (algebraMap Λ B w) = res₀ w)
    (Φ : A →ₐ[Λ] B) : ∀ a : A, rB (Φ a) = rA a := by sorry
