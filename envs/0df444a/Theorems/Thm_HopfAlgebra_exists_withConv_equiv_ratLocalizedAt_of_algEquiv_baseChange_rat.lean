-- Prove2me | Theorems.Thm_HopfAlgebra_exists_withConv_equiv_ratLocalizedAt_of_algEquiv_baseChange_rat
-- name    : HopfAlgebra.exists_withConv_equiv_ratLocalizedAt_of_algEquiv_baseChange_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/edc82215-bd18-5fcb-abc3-01181db04cfd
-- title:
--   Transport of ℚ̄-points along a base-change isomorphism
-- statement:
--   Fix a prime $p$ and write $\mathbb{Z}_{(p)} =$ [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) for the subring of $\mathbb{Q}$ consisting of those rationals whose denominator is coprime to $p$. Let $N$ be an additive commutative group carrying a distributive multiplicative action of the group $G = \mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ of $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ`. Let $A$ be a commutative ring with a Hopf algebra structure over $\mathbb{Q}$, and let $eA$ be a bijection from `WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ)`, the set of $\mathbb{Q}$-algebra maps $A \to \overline{\mathbb{Q}}$ equipped with the convolution product, onto $N$, such that $eA(f\cdot g) = eA(f) + eA(g)$ for all $f,g$, and such that for every $\sigma \in G$ and all $f,g$ with $g(a) = \sigma(f(a))$ for all $a \in A$ one has $eA(g) = \sigma \cdot eA(f)$. Let $H$ be a commutative ring with a Hopf algebra structure over $\mathbb{Z}_{(p)}$, and let $\psi \colon \mathbb{Q} \otimes_{\mathbb{Z}_{(p)}} H \to A$ be an isomorphism of $\mathbb{Q}$-algebras which is compatible with comultiplication, in the sense that $\mathrm{comul}(\psi x) = (\psi \otimes \psi)(\mathrm{comul}\, x)$ for all $x$, the comultiplications being taken over $\mathbb{Q}$. Then there exists a bijection $e$ from `WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)` onto $N$ satisfying $e(f\cdot g) = e(f) + e(g)$ for all $f,g$, and $e(g) = \sigma \cdot e(f)$ whenever $\sigma \in G$ and $g(h) = \sigma(f(h))$ for all $h \in H$.
--
--   This is the generic-fibre half of the transport of the group of $\overline{\mathbb{Q}}$-points of a Hopf algebra along a base-change isomorphism: the Galois-equivariant identification of the convolution monoid of $\overline{\mathbb{Q}}$-points of the $\mathbb{Q}$-Hopf algebra $A$ with $N$ is moved to the $\mathbb{Z}_{(p)}$-Hopf algebra $H$ whose generic fibre is $A$. It is used by [`HopfAlgebra.exists_finiteFlat_ratLocalizedAt_of_algEquiv_baseChange_padic`](thm.html#HopfAlgebra.exists_finiteFlat_ratLocalizedAt_of_algEquiv_baseChange_padic), in the construction of finite flat models over $\mathbb{Z}_{(p)}$ of a given Galois module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_withConv_equiv_ratLocalizedAt_of_algEquiv_baseChange_rat.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NNReal TensorProduct
open scoped TensorProduct in

theorem HopfAlgebra.exists_withConv_equiv_ratLocalizedAt_of_algEquiv_baseChange_rat
    (p : ℕ) [Fact p.Prime]
    {N : Type} [AddCommGroup N]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) N]
    (A : Type) [CommRing A] [HopfAlgebra ℚ A]
    (eA : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ) ≃ N)
    (heA_add : ∀ f g, eA (f * g) = eA f + eA g)
    (heA_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (A →ₐ[ℚ] AlgebraicClosure ℚ)),
      (∀ a : A, g a = σ (f a)) → eA g = σ • (eA f))
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    (ψ : (ℚ ⊗[(GaloisRep.ratLocalizedAt p)] H) ≃ₐ[ℚ] A)
    (hψcomul : ∀ x, Coalgebra.comul (R := ℚ) (ψ x) =
        (TensorProduct.map ψ.toLinearMap ψ.toLinearMap) (Coalgebra.comul (R := ℚ) x)) :
    ∃ e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ N,
      (∀ f g, e (f * g) = e f + e g) ∧
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
        (∀ h : H, g h = σ (f h)) → e g = σ • (e f) := by sorry
