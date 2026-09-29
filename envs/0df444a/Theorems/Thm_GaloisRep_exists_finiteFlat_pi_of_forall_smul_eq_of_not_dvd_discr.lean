-- Prove2me | Theorems.Thm_GaloisRep_exists_finiteFlat_pi_of_forall_smul_eq_of_not_dvd_discr
-- name    : GaloisRep.exists_finiteFlat_pi_of_forall_smul_eq_of_not_dvd_discr
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/bda1d0aa-efd7-53c0-b177-f8ee12e25fd8
-- title:
--   Weil restriction of a finite flat group scheme along an unramified Galois set
-- statement:
--   Let $p$ be a prime and write $\mathbb{Z}_{(p)}$ for the subring [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of those rationals whose denominator is coprime to $p$. Let $G$ be a commutative ring carrying a Hopf algebra structure over $\mathbb{Z}_{(p)}$ which is finite and flat as a $\mathbb{Z}_{(p)}$-module and whose comultiplication is cocommutative. Let $M$ be an additive commutative group with a distributive action of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, realised as the $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ`, and let $e$ be a bijection from the type of $\mathbb{Z}_{(p)}$-algebra homomorphisms $G \to \overline{\mathbb{Q}}$, taken with its convolution multiplication, onto $M$, such that $e(f*g) = e(f)+e(g)$, and such that whenever $g = \sigma \circ f$ pointwise on $G$ one has $e(g) = \sigma \cdot e(f)$. Let $S$ be a finite type with an action of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, and let $K \subset \overline{\mathbb{Q}}$ be a finite Galois extension of $\mathbb{Q}$ whose discriminant, as a number field, is not divisible by $p$, and such that every $\sigma$ fixing $K$ pointwise acts trivially on $S$. Then there exists a commutative ring $H$ with a Hopf algebra structure over $\mathbb{Z}_{(p)}$ that is finite, flat and cocommutative, together with a bijection $e'$ from the convolution monoid of $\mathbb{Z}_{(p)}$-algebra homomorphisms $H \to \overline{\mathbb{Q}}$ onto the group $S \to M$ of $M$-valued functions on $S$, satisfying $e'(f*g) = e'(f)+e'(g)$ and, whenever $g = \sigma \circ f$ pointwise on $H$, $e'(g)(s) = \sigma \cdot \bigl(e'(f)(\sigma^{-1}\cdot s)\bigr)$ for all $s \in S$.
--
--   This is the construction of the Weil restriction to $\mathbb{Z}_{(p)}$ of the base change of the finite flat commutative group scheme $\operatorname{Spec} G$ along the finite étale $\mathbb{Z}_{(p)}$-algebra attached to the Galois set $S$, the hypothesis $p \nmid d_K$ guaranteeing étaleness; on points it produces the Galois module induced from $M$ by the permutation set $S$. It is used to verify flatness at $p$ of residual and twisted Galois representations, and in the construction of finite flat prolongations of torsion in Jacobians of modular curves with diamond twists.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_exists_finiteFlat_pi_of_forall_smul_eq_of_not_dvd_discr.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem GaloisRep.exists_finiteFlat_pi_of_forall_smul_eq_of_not_dvd_discr
    (p : ℕ) (hp : p.Prime)
    (G : Type) [CommRing G] [HopfAlgebra (GaloisRep.ratLocalizedAt p) G]
    [Module.Finite (GaloisRep.ratLocalizedAt p) G] [Module.Flat (GaloisRep.ratLocalizedAt p) G]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) G]
    {M : Type} [AddCommGroup M] [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) M]
    (e : WithConv (G →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ M)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (G →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ x : G, g x = σ (f x)) → e g = σ • (e f))
    {S : Type} [Finite S] [MulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) S]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (hK : haveI : NumberField K := @NumberField.mk _ _ inferInstance ‹FiniteDimensional ℚ K›
      ¬ (p : ℤ) ∣ NumberField.discr K)
    (hS : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ K, σ x = x) →
      ∀ s : S, σ • s = s) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) H),
      Module.Finite (GaloisRep.ratLocalizedAt p) H ∧ Module.Flat (GaloisRep.ratLocalizedAt p) H ∧
      Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H ∧
      ∃ e' : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ (S → M),
        (∀ f g, e' (f * g) = e' f + e' g) ∧
        ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
          (∀ x : H, g x = σ (f x)) → ∀ s : S, e' g s = σ • (e' f (σ⁻¹ • s)) := by sorry
