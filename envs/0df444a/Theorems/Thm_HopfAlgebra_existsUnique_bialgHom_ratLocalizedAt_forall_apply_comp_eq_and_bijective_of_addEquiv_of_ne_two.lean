-- Prove2me | Theorems.Thm_HopfAlgebra_existsUnique_bialgHom_ratLocalizedAt_forall_apply_comp_eq_and_bijective_of_addEquiv_of_ne_two
-- name    : HopfAlgebra.existsUnique_bialgHom_ratLocalizedAt_forall_apply_comp_eq_and_bijective_of_addEquiv_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/c99f9cb9-2ed5-5066-a1a4-a5c27d72e7de
-- title:
--   Raynaud prolongation over ℤ₍ₚ₎: points form, p ≠ 2
-- statement:
--   Let $p$ be a prime with $p \neq 2$, and write $R =$ [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) for the subring of $\mathbb{Q}$ consisting of those rationals whose denominator is coprime to $p$. Let $M_1, M_2$ be additive commutative groups each carrying a distributive multiplicative action of the group $\overline{\mathbb{Q}} \simeq_{\mathrm{alg}[\mathbb{Q}]} \overline{\mathbb{Q}}$ of $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ`. For $i = 1, 2$ let $H_i$ be a commutative ring that is a Hopf algebra over $R$, finite and free as an $R$-module, cocommutative as an $R$-coalgebra, and of $R$-rank $p^{a_i}$ for some natural number $a_i$; let $e_i$ be a bijection from `WithConv` of the set of $R$-algebra homomorphisms $H_i \to \overline{\mathbb{Q}}$ (that is, the type synonym carrying the convolution product) onto $M_i$ which sends the convolution product to addition, $e_i(f \cdot g) = e_i f + e_i g$, and which is Galois-equivariant in the sense that whenever $g\,x = \sigma(f\,x)$ for all $x \in H_i$ one has $e_i g = \sigma \cdot e_i f$. Let $\varphi : M_1 \to M_2$ be an additive equivalence with $\varphi(\sigma \cdot m) = \sigma \cdot \varphi(m)$ for all $\sigma$ and $m$. Then, first, there is exactly one bialgebra homomorphism $g : H_2 \to H_1$ over $R$ such that $e_2$ of the convolution-class of $f \circ g$ equals $\varphi(e_1 f)$ for every point $f$ of $H_1$; and, second, every bialgebra homomorphism $g : H_2 \to H_1$ over $R$ with that property is bijective.
--
--   This is Raynaud's uniqueness of prolongations for finite flat group schemes of $p$-power order at absolute ramification $e = 1 < p-1$, here over $\mathbb{Z}_{(p)}$ and phrased in terms of $\overline{\mathbb{Q}}$-points rather than schemes: a Galois-equivariant isomorphism of point groups is induced by a unique bialgebra map, and that map is an isomorphism. It specialises the corresponding statement over an arbitrary characteristic-zero discrete valuation ring with $p$ irreducible, and is used in the Dieudonné-module computations (surjectivity onto the bottom layer, and the comparison of the kernel of Frobenius with the cokernel of Verschiebung) and in the identification of the Cartier dual of the torsion of the model at $j = 0$ on the modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_existsUnique_bialgHom_ratLocalizedAt_forall_apply_comp_eq_and_bijective_of_addEquiv_of_ne_two.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem HopfAlgebra.existsUnique_bialgHom_ratLocalizedAt_forall_apply_comp_eq_and_bijective_of_addEquiv_of_ne_two
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    {M₁ M₂ : Type} [AddCommGroup M₁] [AddCommGroup M₂]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) M₁]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) M₂]
    (H₁ : Type) [CommRing H₁] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H₁]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H₁] [Module.Free (GaloisRep.ratLocalizedAt p) H₁]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H₁]
    (hrank₁ : ∃ a : ℕ, Module.finrank (GaloisRep.ratLocalizedAt p) H₁ = p ^ a)
    (e₁ : WithConv (H₁ →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ M₁)
    (he₁_add : ∀ f g, e₁ (f * g) = e₁ f + e₁ g)
    (he₁_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (H₁ →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ x : H₁, g x = σ (f x)) → e₁ g = σ • e₁ f)
    (H₂ : Type) [CommRing H₂] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H₂]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H₂] [Module.Free (GaloisRep.ratLocalizedAt p) H₂]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H₂]
    (hrank₂ : ∃ a : ℕ, Module.finrank (GaloisRep.ratLocalizedAt p) H₂ = p ^ a)
    (e₂ : WithConv (H₂ →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ M₂)
    (he₂_add : ∀ f g, e₂ (f * g) = e₂ f + e₂ g)
    (he₂_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (H₂ →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ x : H₂, g x = σ (f x)) → e₂ g = σ • e₂ f)
    (φ : M₁ ≃+ M₂)
    (hφ : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (m : M₁), φ (σ • m) = σ • φ m) :
    (∃! g : H₂ →ₐc[GaloisRep.ratLocalizedAt p] H₁,
      ∀ f : WithConv (H₁ →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        e₂ (WithConv.toConv ((WithConv.ofConv f).comp (g : H₂ →ₐ[GaloisRep.ratLocalizedAt p] H₁))) = φ (e₁ f)) ∧
    (∀ g : H₂ →ₐc[GaloisRep.ratLocalizedAt p] H₁,
      (∀ f : WithConv (H₁ →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        e₂ (WithConv.toConv ((WithConv.ofConv f).comp (g : H₂ →ₐ[GaloisRep.ratLocalizedAt p] H₁))) = φ (e₁ f)) →
      Function.Bijective g) := by sorry
