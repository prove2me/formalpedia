-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_existsUnique_comp_eq_of_isTorsionPoint_of_torsion_points_equiv
-- name    : GoodReductionJacobian.RelativeGroupLaw.existsUnique_comp_eq_of_isTorsionPoint_of_torsion_points_equiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/d5d2a9c0-ac1e-5d01-90a8-22061f020e71
-- title:
--   Spec H represents the n-torsion functor on all schemes
-- statement:
--   Let $K$ be a field, $A$ a scheme and $f \colon A \to \operatorname{Spec} K$, and let $L$ be a relative group law for $f$: a functorial group structure on the sets $\mathrm{SchemeHomOver}\,t\,f = \{\varphi \colon T \to A \mid \varphi \text{ followed by } f = t\}$ of points over arbitrary $t \colon T \to \operatorname{Spec} K$, given by operations `mul`, `one`, `inv` satisfying associativity, the unit laws, left inverse, and compatibility of `mul` with precomposition by a morphism over $\operatorname{Spec} K$. Assume $L$ is commutative, and let $n \in \mathbb{N}$ be such that the endomorphism $N =$ `L.schemeNsmul n` of $A$ (the underlying morphism of the $n$-fold sum of the identity point) is finite and flat. Let $H$ be a commutative ring that is a cocommutative Hopf algebra over $K$, finite as a $K$-module, together with, for every commutative $K$-algebra $T$, a bijection $e_T$ from the convolution monoid `WithConv` $(H \to_{\mathrm{alg}[K]} T)$ onto the set of $x \in \mathrm{SchemeHomOver}\,(\operatorname{Spec}(K \to T))\,f$ with $n$-fold sum equal to the unit point; assume $e_T$ carries the convolution product to `L.mul`, and that it is natural: for $g' \colon T \to T'$ over $K$ and $\varphi$, the point $e_{T'}(g' \circ \varphi)$ has underlying morphism $\operatorname{Spec}(g')$ followed by that of $e_T(\varphi)$. Write $u$ for the underlying morphism of $e_H(\mathrm{id}_H)$. Then for every $t \colon T \to \operatorname{Spec} K$ and every point $z$ of $A$ over $t$ whose $n$-fold sum is the unit point, there is a unique $g \colon T \to \operatorname{Spec} H$ with $g$ followed by $u$ equal to the underlying morphism of $z$.
--
--   This is the representability statement that the finite $K$-scheme $\operatorname{Spec} H$, with its distinguished point $e_H(\mathrm{id}_H)$, is the kernel of multiplication by $n$ as a functor on all $K$-schemes, not merely on affine ones: $e_H(\mathrm{id}_H)$ is a universal $n$-torsion point. It upgrades a bijection of points over affine test algebras to a universal property over arbitrary bases, and is used in the construction of the $n$-torsion group-scheme action, via [`GoodReductionJacobian.RelativeGroupLaw.exists_action_isIso_shear_of_torsion_points_equiv`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_action_isIso_shear_of_torsion_points_equiv).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_existsUnique_comp_eq_of_isTorsionPoint_of_torsion_points_equiv.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.existsUnique_comp_eq_of_isTorsionPoint_of_torsion_points_equiv
    (K : Type u) [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative)
    (n : ℕ) (hfin : IsFinite (L.schemeNsmul n)) (hflat : Flat (L.schemeNsmul n))
    (H : Type u) [CommRing H] [HopfAlgebra K H] [Module.Finite K H] [Coalgebra.IsCocomm K H]
    (e : ∀ (T : Type u) [CommRing T] [Algebra K T],
      WithConv (H →ₐ[K] T) ≃ L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap K T))) n)
    (he_mul : ∀ (T : Type u) [CommRing T] [Algebra K T] (φ ψ : WithConv (H →ₐ[K] T)),
      ((e T (φ * ψ)).val : SchemeHomOver _ f) = L.mul _ (e T φ).val (e T ψ).val)
    (he_nat : ∀ (T T' : Type u) [CommRing T] [Algebra K T] [CommRing T'] [Algebra K T']
        (g' : T →ₐ[K] T') (φ : WithConv (H →ₐ[K] T)),
      ((e T' (.toConv (g'.comp φ.ofConv))).val : SchemeHomOver _ f).1 =
        Spec.map (CommRingCat.ofHom g'.toRingHom) ≫ (e T φ).val.1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (z : SchemeHomOver t f) (hz : L.IsTorsionPoint t n z) :
    ∃! g : T ⟶ Spec (CommRingCat.of H), g ≫ (e H (.toConv (AlgHom.id K H))).val.1 = z.1 := by sorry
