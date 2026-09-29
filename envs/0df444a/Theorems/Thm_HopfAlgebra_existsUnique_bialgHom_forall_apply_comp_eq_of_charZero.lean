-- Prove2me | Theorems.Thm_HopfAlgebra_existsUnique_bialgHom_forall_apply_comp_eq_of_charZero
-- name    : HopfAlgebra.existsUnique_bialgHom_forall_apply_comp_eq_of_charZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/b147c01d-3c2d-51ba-914c-2c5612db2f59
-- title:
--   Full faithfulness of ̄ K-points of finite Hopf algebras
-- statement:
--   Let $K$ be a field of characteristic zero and $\bar K$ an algebraic closure of it, and write $\mathrm{Gal} = \bar K \simeq_{\mathrm{alg}[K]} \bar K$ for its group of $K$-algebra automorphisms. Let $M_1, M_2$ be additive commutative groups carrying distributive multiplicative actions of $\mathrm{Gal}$. Let $E_1$ and $E_2$ be commutative rings equipped with Hopf algebra structures over $K$ and finite as $K$-modules. Suppose given bijections $e_i \colon \mathrm{WithConv}(E_i \to_{\mathrm{alg}[K]} \bar K) \simeq M_i$ from the $K$-algebra maps $E_i \to \bar K$, regarded as the convolution monoid, to $M_i$ ($i = 1,2$), such that each $e_i$ sends convolution products to sums, $e_i(f \ast g) = e_i f + e_i g$, and is Galois-equivariant in the sense that whenever $\sigma \in \mathrm{Gal}$ and points $f, g$ satisfy $g(x) = \sigma(f(x))$ for all $x \in E_i$, one has $e_i g = \sigma \cdot e_i f$. Let $\varphi \colon M_1 \to M_2$ be an additive group homomorphism with $\varphi(\sigma \cdot m) = \sigma \cdot \varphi(m)$ for all $\sigma$ and $m$. Then there is a unique $K$-bialgebra homomorphism $\psi \colon E_2 \to E_1$ such that for every point $f \colon E_1 \to \bar K$ one has $e_2(f \circ \psi) = \varphi(e_1 f)$.
--
--   This is the full faithfulness of the points functor $G \mapsto G(\bar K)$ from finite commutative group schemes over a field of characteristic zero (where such schemes are étale, by Cartier's theorem) to finite Galois modules; no cocommutativity of $E_1, E_2$ is assumed, it being forced by the additivity of the identifications $e_1, e_2$ of points. It is the tool used to transport a map of Galois modules into a map of the corresponding finite Hopf algebras, and is invoked by the comparison results for Hopf algebras whose rank is a prime power.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_existsUnique_bialgHom_forall_apply_comp_eq_of_charZero.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HopfAlgebra.existsUnique_bialgHom_forall_apply_comp_eq_of_charZero
    (K : Type) [Field K] [CharZero K] (Kbar : Type) [Field Kbar] [Algebra K Kbar] [IsAlgClosure K Kbar]
    {M₁ M₂ : Type} [AddCommGroup M₁] [AddCommGroup M₂]
    [DistribMulAction (Kbar ≃ₐ[K] Kbar) M₁] [DistribMulAction (Kbar ≃ₐ[K] Kbar) M₂]
    (E₁ : Type) [CommRing E₁] [HopfAlgebra K E₁] [Module.Finite K E₁]
    (e₁ : WithConv (E₁ →ₐ[K] Kbar) ≃ M₁)
    (he₁_add : ∀ f g, e₁ (f * g) = e₁ f + e₁ g)
    (he₁_act : ∀ (σ : Kbar ≃ₐ[K] Kbar) (f g : WithConv (E₁ →ₐ[K] Kbar)),
      (∀ x : E₁, g x = σ (f x)) → e₁ g = σ • (e₁ f))
    (E₂ : Type) [CommRing E₂] [HopfAlgebra K E₂] [Module.Finite K E₂]
    (e₂ : WithConv (E₂ →ₐ[K] Kbar) ≃ M₂)
    (he₂_add : ∀ f g, e₂ (f * g) = e₂ f + e₂ g)
    (he₂_act : ∀ (σ : Kbar ≃ₐ[K] Kbar) (f g : WithConv (E₂ →ₐ[K] Kbar)),
      (∀ x : E₂, g x = σ (f x)) → e₂ g = σ • (e₂ f))
    (φ : M₁ →+ M₂)
    (hφ : ∀ (σ : Kbar ≃ₐ[K] Kbar) (m : M₁), φ (σ • m) = σ • φ m) :
    ∃! ψ : E₂ →ₐc[K] E₁,
      ∀ f : WithConv (E₁ →ₐ[K] Kbar),
        e₂ (WithConv.toConv ((WithConv.ofConv f).comp (ψ : E₂ →ₐ[K] E₁))) = φ (e₁ f) := by sorry
