-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_eq_comp_of_hom_spec_laurentPolynomial
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_eq_comp_of_hom_spec_laurentPolynomial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/d721cdab-7d71-557c-b42e-4b0699cf7665
-- title:
--   Morphisms G_m → A into an abelian scheme are constant
-- statement:
--   Let $k$ be a field and let $f : A \to \operatorname{Spec} k$ be a morphism of schemes satisfying the property bundle `AbelianSchemePropertyBundle`, that is: $f$ is smooth, $f$ is proper, for every point $s$ of $\operatorname{Spec} k$ the fibre $f^{-1}(s)$ of the underlying continuous map is a connected topological space, and there exists a relative group law for $f$ over $k$ — a functorial group structure on the sets of $T$-points of $A$ over $\operatorname{Spec} k$, given by multiplication, unit and inverse operations on sections, subject to associativity, the two unit laws, the left inverse law, and naturality under base change along morphisms $T' \to T$ over $\operatorname{Spec} k$. Let $\varphi : \operatorname{Spec} k[t,t^{-1}] \to A$ be a morphism whose composite with $f$ is the structure morphism $\operatorname{Spec}$ of the algebra map $k \to k[t,t^{-1}]$, so that $\varphi$ is a morphism of $k$-schemes from $\mathbf{G}_m$ to $A$. Then there is a $k$-point $a : \operatorname{Spec} k \to A$, i.e. a morphism with $a$ followed by $f$ equal to the identity of $\operatorname{Spec} k$, such that $\varphi$ equals the structure morphism $\operatorname{Spec} k[t,t^{-1}] \to \operatorname{Spec} k$ followed by $a$; in other words $\varphi$ is constant.
--
--   This is the statement that an abelian variety contains no rational curves, in the form that every $k$-morphism from the multiplicative group to $A$ factors through a $k$-rational point; no group-law hypothesis is imposed on the source, so the usual triviality of homomorphisms from a split torus into an abelian variety is a special case. It feeds the corresponding statement for the group algebra of a finite product of copies of $\mathbf{Z}$, used when handling the torus part of a semistable Néron fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_eq_comp_of_hom_spec_laurentPolynomial.lean

import Mathlib
import Definitions.Def_JacJ1Iface

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_eq_comp_of_hom_spec_laurentPolynomial
    {k : Type u} [Field k] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)}
    (hA : AbelianSchemePropertyBundle k f)
    (φ : Spec (CommRingCat.of (LaurentPolynomial k)) ⟶ A)
    (hφ : φ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (LaurentPolynomial k)))) :
    ∃ a : Spec (CommRingCat.of k) ⟶ A, a ≫ f = 𝟙 _ ∧
      φ = Spec.map (CommRingCat.ofHom (algebraMap k (LaurentPolynomial k))) ≫ a := by sorry
