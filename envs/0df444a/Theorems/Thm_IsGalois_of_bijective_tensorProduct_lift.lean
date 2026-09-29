-- Prove2me | Theorems.Thm_IsGalois_of_bijective_tensorProduct_lift
-- name    : IsGalois.of_bijective_tensorProduct_lift
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/3397b65a-b5af-5520-95a2-9dc3ed8b8c42
-- title:
--   Galois base change along a bijective tensor product map
-- statement:
--   Let $K_1$, $K$, $E$, $F$ be fields, with $K$ a $K_1$-algebra that is finite-dimensional over $K_1$ and Galois over $K_1$, with $E$ a $K_1$-algebra, and with $F$ carrying algebra structures over $E$, over $K$ and over $K_1$ such that $F$ is a scalar tower over $K_1$ through $E$ and also a scalar tower over $K_1$ through $K$. Assume that the $E$-algebra homomorphism $E \otimes_{K_1} K \to F$ obtained, via `Algebra.TensorProduct.lift`, from the structure map $E \to F$ and from the $K_1$-algebra map $K \to F$ (the two images commuting because $F$ is commutative) is bijective. Then four conclusions hold simultaneously: $F$ is finite-dimensional over $E$; $F/E$ is Galois; the group $F \simeq_{\mathrm{alg}[E]} F$ of $E$-algebra automorphisms of $F$ is isomorphic, as a group, to the group $K \simeq_{\mathrm{alg}[K_1]} K$ of $K_1$-algebra automorphisms of $K$ (asserted as nonemptiness of the type of such multiplicative isomorphisms); and $\operatorname{finrank}_E F = \operatorname{finrank}_{K_1} K$.
--
--   This is the standard base-change (translation) theorem for Galois extensions, in the form where linear disjointness is expressed by bijectivity of $E \otimes_{K_1} K \to F$: the extension $F/E$ inherits finiteness, the Galois property, the degree and the Galois group of $K/K_1$. It is used in the analysis of completions of a model of a modular curve, to transport a Galois covering of the base to the completed generic fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsGalois_of_bijective_tensorProduct_lift.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem IsGalois.of_bijective_tensorProduct_lift
    {K₁ K E F : Type*} [Field K₁] [Field K] [Field E] [Field F]
    [Algebra K₁ K] [FiniteDimensional K₁ K] [IsGalois K₁ K]
    [Algebra K₁ E] [Algebra E F] [Algebra K F] [Algebra K₁ F]
    [IsScalarTower K₁ E F] [IsScalarTower K₁ K F]
    (h : Function.Bijective
      (Algebra.TensorProduct.lift (Algebra.ofId E F) (IsScalarTower.toAlgHom K₁ K F)
        (fun _ _ => Commute.all _ _) : E ⊗[K₁] K →ₐ[E] F)) :
    FiniteDimensional E F ∧ IsGalois E F ∧
      Nonempty ((F ≃ₐ[E] F) ≃* (K ≃ₐ[K₁] K)) ∧
      Module.finrank E F = Module.finrank K₁ K := by sorry
