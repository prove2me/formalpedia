-- Prove2me | Theorems.Thm_GaloisRep_exists_bialgHom_surjective_finiteFlat_model_addSubgroup_of_stable
-- name    : GaloisRep.exists_bialgHom_surjective_finiteFlat_model_addSubgroup_of_stable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/d3e42d2d-8714-5b42-9985-a531d59518e2
-- title:
--   Schematic closure of a stable subgroup as Hopf quotient
-- statement:
--   Fix a prime $p$ and write $R = \mathbb{Z}_{(p)}$ for the subring [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of the rationals whose denominator is coprime to $p$. Let $H$ be a commutative ring carrying an $R$-Hopf algebra structure which is finite and free as an $R$-module and cocommutative as a coalgebra, and let $N$ be an additive commutative group with a distributive multiplicative action of $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, realised as the $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ`. Assume given a bijection $e$ from the convolution monoid `WithConv` of $R$-algebra maps $H \to \overline{\mathbb{Q}}$ onto $N$ such that $e(fg) = e(f) + e(g)$ for all $f,g$, and such that $e$ is Galois-equivariant in the following pointwise form: whenever $g(h) = \sigma(f(h))$ for all $h \in H$, one has $e(g) = \sigma \cdot e(f)$. Let $T$ be a type indexing additive endomorphisms $\mathrm{act}(t)$ of $N$ and $R$-algebra endomorphisms $\varphi(t)$ of $H$ compatible under $e$ in the same pointwise sense: if $g(h) = f(\varphi(t)(h))$ for all $h$, then $e(g) = \mathrm{act}(t)(e(f))$. Finally let $N' \le N$ be an additive subgroup stable under the Galois action and under every $\mathrm{act}(t)$. The conclusion asserts the existence of a commutative ring $H'$ with an $R$-Hopf algebra structure, finite and free over $R$ and cocommutative, together with a surjective $R$-bialgebra map $\pi : H \to H'$, a bijection $e'$ from the convolution monoid of $R$-algebra maps $H' \to \overline{\mathbb{Q}}$ onto the subgroup $N'$, and $R$-algebra endomorphisms $\varphi'(t)$ of $H'$ for $t \in T$, such that $e'(f)$, viewed in $N$, equals $e(f \circ \pi)$ for every such $f$, and such that $\varphi'(t) \circ \pi = \pi \circ \varphi(t)$ for every $t \in T$.
--
--   This is the schematic closure of a Galois- and operator-stable subgroup $N'$ of the generic fibre of a finite flat group scheme over $\mathbb{Z}_{(p)}$, presented dually as a Hopf-algebra quotient $H \twoheadrightarrow H'$ carrying the induced operators. It is used in the construction of the bottom layer of a Dieudonné-module argument, in [`Deformation.DieudonneModule.exists_surjective_ker_map_of_bottomLayer`](thm.html#Deformation.DieudonneModule.exists_surjective_ker_map_of_bottomLayer), which closes off a further subgroup inside such a quotient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_exists_bialgHom_surjective_finiteFlat_model_addSubgroup_of_stable.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem GaloisRep.exists_bialgHom_surjective_finiteFlat_model_addSubgroup_of_stable
    (p : ℕ) [Fact p.Prime]
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Free (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
    {N : Type} [AddCommGroup N] [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) N]
    (e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ N)
    (he_add : ∀ f g, e (f * g) = e f + e g)
    (he_gal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ h : H, g h = σ (f h)) → e g = σ • e f)
    {T : Type} (act : T → (N →+ N)) (φ : T → (H →ₐ[GaloisRep.ratLocalizedAt p] H))
    (hφ : ∀ (t : T) (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ h : H, g h = f (φ t h)) → e g = act t (e f))
    (N' : AddSubgroup N)
    (hN'gal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), ∀ x ∈ N', σ • x ∈ N')
    (hN'act : ∀ t : T, ∀ x ∈ N', act t x ∈ N') :
    ∃ (H' : Type) (_ : CommRing H') (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) H')
      (_ : Module.Finite (GaloisRep.ratLocalizedAt p) H') (_ : Module.Free (GaloisRep.ratLocalizedAt p) H')
      (_ : Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H')
      (π : H →ₐc[GaloisRep.ratLocalizedAt p] H')
      (e' : WithConv (H' →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ ↥N')
      (φ' : T → (H' →ₐ[GaloisRep.ratLocalizedAt p] H')),
      Function.Surjective π ∧
      (∀ f : WithConv (H' →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        ((e' f : ↥N') : N) =
          e (WithConv.toConv ((WithConv.ofConv f).comp (π : H →ₐ[GaloisRep.ratLocalizedAt p] H')))) ∧
      (∀ t : T, (φ' t).comp (π : H →ₐ[GaloisRep.ratLocalizedAt p] H') =
        (π : H →ₐ[GaloisRep.ratLocalizedAt p] H').comp (φ t)) := by sorry
