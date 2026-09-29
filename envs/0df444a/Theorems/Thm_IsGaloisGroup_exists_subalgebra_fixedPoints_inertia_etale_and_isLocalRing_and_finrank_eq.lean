-- Prove2me | Theorems.Thm_IsGaloisGroup_exists_subalgebra_fixedPoints_inertia_etale_and_isLocalRing_and_finrank_eq
-- name    : IsGaloisGroup.exists_subalgebra_fixedPoints_inertia_etale_and_isLocalRing_and_finrank_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/2841ad1e-c787-5236-b1be-99151a20376e
-- title:
--   Inertia ring is finite étale with full residue field
-- statement:
--   Let $A$ be a commutative Noetherian local domain which is integrally closed and complete for the adic topology of its maximal ideal, and let $B$ be a commutative local domain which is an $A$-algebra, module-finite over $A$, with $A \to B$ injective (`FaithfulSMul A B`) and a local homomorphism. Let $D$ be a finite group acting on $B$ by ring automorphisms which is a Galois group for $A \to B$ in the sense of `IsGaloisGroup D A B`: the action is faithful, commutes with the $A$-action, and $A$ is exactly the ring of $D$-invariants of $B$. Assume the residue field extension $\kappa(B)/\kappa(A)$ is separable. Write $I = (\mathfrak m_B).\mathrm{inertia}\,D$ for the inertia subgroup of the maximal ideal of $B$, the subgroup of those $d \in D$ with $d \cdot b - b \in \mathfrak m_B$ for all $b \in B$. Then there is an $A$-subalgebra $B_1 \subseteq B$ whose elements are precisely the elements of $B$ fixed by every element of $I$, such that: $I$ is a Galois group for $B_1 \to B$; $B_1$ is étale over $A$ (formally étale and of finite presentation); $B_1$ is local; the composite $B_1 \hookrightarrow B \to \kappa(B)$ is surjective; $B_1$ is free as an $A$-module; $\operatorname{rank}_A B_1 = [\kappa(B):\kappa(A)]$; and the index of $I$ in $D$ equals $[\kappa(B):\kappa(A)]$.
--
--   This is the classical statement that the inertia ring $B^{I}$ of a finite group acting on a local ring is unramified — here finite étale — over the invariant ring, local with residue field all of $\kappa(B)$, and free of rank the residue degree, which also equals the index of the inertia subgroup. It is used in the identification of adic completions of invariant rings, both for regular local rings and for the crossing models of modular curves, where $B^{I}$ plays the role of the unramified part $\widehat{\mathcal O} \otimes_{W(\kappa)} W(\kappa')$ of the extension.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsGaloisGroup_exists_subalgebra_fixedPoints_inertia_etale_and_isLocalRing_and_finrank_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Pointwise

theorem IsGaloisGroup.exists_subalgebra_fixedPoints_inertia_etale_and_isLocalRing_and_finrank_eq
    {A B : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [IsIntegrallyClosed A]
    [CommRing B] [IsDomain B] [IsLocalRing B]
    [Algebra A B] [Module.Finite A B] [FaithfulSMul A B] [IsLocalHom (algebraMap A B)]
    (D : Type*) [Group D] [Finite D] [MulSemiringAction D B] [IsGaloisGroup D A B]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)] :
    ∃ B₁ : Subalgebra A B,
      (∀ b : B, b ∈ B₁ ↔ ∀ d ∈ (IsLocalRing.maximalIdeal B).inertia D, d • b = b) ∧
      IsGaloisGroup ↥((IsLocalRing.maximalIdeal B).inertia D) ↥B₁ B ∧
      Algebra.Etale A ↥B₁ ∧ IsLocalRing ↥B₁ ∧
      Function.Surjective (fun b₁ : ↥B₁ => IsLocalRing.residue B (b₁ : B)) ∧
      Module.Free A ↥B₁ ∧
      Module.finrank A ↥B₁ =
        Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) ∧
      ((IsLocalRing.maximalIdeal B).inertia D).index =
        Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) := by sorry
