-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_eq_comp_of_hom_spec_polynomial
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_eq_comp_of_hom_spec_polynomial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/5ef2408b-e3be-5649-8a0c-fb1dda6d70b3
-- title:
--   Every k-morphism A¹_k → A into an abelian scheme is constant
-- statement:
--   Let $k$ be a field, let $A$ be a scheme and let $f : A \to \operatorname{Spec} k$ be a morphism satisfying the property bundle `AbelianSchemePropertyBundle`, that is: $f$ is smooth, $f$ is proper, for every point $s$ of $\operatorname{Spec} k$ the fibre $f^{-1}(s)$ of the underlying continuous map is connected (and non-empty), and there exists a relative group law for $f$ over $k$, namely multiplication, unit and inversion operations on the sets of $T$-points $\{x : T \to A \mid x \text{ over } t\}$ for every $k$-scheme $t : T \to \operatorname{Spec} k$, satisfying associativity, the unit laws and left inverses, and natural with respect to base-compatible morphisms $T' \to T$. Let $\psi : \operatorname{Spec} k[X] \to A$ be a morphism whose composite with $f$ is the structure morphism $\operatorname{Spec} k[X] \to \operatorname{Spec} k$ induced by $k \to k[X]$, i.e. $\psi$ is a morphism of $k$-schemes from the affine line. Then there is a section $a : \operatorname{Spec} k \to A$ of $f$, so $a$ followed by $f$ is the identity of $\operatorname{Spec} k$, such that $\psi$ equals the structure morphism $\operatorname{Spec} k[X] \to \operatorname{Spec} k$ followed by $a$; that is, $\psi$ is the constant morphism at the $k$-rational point $a$.
--
--   This is the statement that an abelian variety contains no affine line, in the form that every $k$-morphism $\mathbf{A}^1_k \to A$ factors through a $k$-rational point. It is used to deduce the multiplicative-group analogue, that every $k$-morphism $\operatorname{Spec} k[X, X^{-1}] \to A$ is constant, by first extending such a morphism across the origin using properness.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_eq_comp_of_hom_spec_polynomial.lean

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

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_eq_comp_of_hom_spec_polynomial
    {k : Type u} [Field k] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)}
    (hA : AbelianSchemePropertyBundle k f)
    (ψ : Spec (CommRingCat.of (Polynomial k)) ⟶ A)
    (hψ : ψ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)))) :
    ∃ a : Spec (CommRingCat.of k) ⟶ A, a ≫ f = 𝟙 _ ∧
      ψ = Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) ≫ a := by sorry
