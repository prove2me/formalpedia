-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_bijective_appTop_fibre_of_isPullback
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.bijective_appTop_fibre_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/11859ab9-c13a-5de8-a9b1-1001c56c3512
-- title:
--   Global functions on a fibre of an abelian scheme
-- statement:
--   Let $T$ be a commutative ring and let $f_0 \colon A_0 \to \operatorname{Spec} T$ be a morphism of schemes satisfying the predicate `AbelianSchemePropertyBundle T f₀`, that is: $f_0$ is smooth, $f_0$ is proper, for every point $s$ of $\operatorname{Spec} T$ the fibre of the underlying continuous map of $f_0$ over $s$ is connected (in particular nonempty), and there exists a relative group law for $f_0$, i.e. a functorial group structure on the sets of $\operatorname{Spec} T$-morphisms $T' \to A_0$ (a multiplication, a unit and an inverse for each $\operatorname{Spec} T$-scheme, satisfying associativity, the two unit laws and the left inverse law, and compatible with composition along morphisms of $\operatorname{Spec} T$-schemes). Let $k$ be a field, $\rho \colon T \to k$ a ring homomorphism, and let $f_k \colon A_k \to \operatorname{Spec} k$ and $i_0 \colon A_k \to A_0$ be morphisms such that the square formed by $i_0$, $f_k$, $f_0$ and $\operatorname{Spec} \rho$ is a pullback square. Then the ring homomorphism $k \to \Gamma(A_k, \mathcal{O}_{A_k})$ obtained from the inverse of the canonical isomorphism $\Gamma(\operatorname{Spec} k, \mathcal{O}) \cong k$ followed by the action of $f_k$ on global sections is bijective.
--
--   This is the standard statement that an abelian variety over a field $k$, here realised as an arbitrary fibre $A_k$ of an abelian scheme over $\operatorname{Spec} T$ along a ring map $T \to k$, has only the constants as global regular functions. It is used in the treatment of relative $\mathrm{Pic}^0$ and of abelian schemes, for instance in identifying units and trivialisations of line bundles on such fibres and in the deformation-theoretic arguments for fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_bijective_appTop_fibre_of_isPullback.lean

import Mathlib
import Definitions.Def_JacJ1Iface

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry

universe u

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.bijective_appTop_fibre_of_isPullback
    {T : Type u} [CommRing T] {A₀ : Scheme.{u}} {f₀ : A₀ ⟶ Spec (CommRingCat.of T)}
    (h₀ : AbelianSchemePropertyBundle T f₀)
    {k : Type u} [Field k] (ρ : T →+* k)
    {Ak : Scheme.{u}} (fk : Ak ⟶ Spec (CommRingCat.of k)) (i₀ : Ak ⟶ A₀)
    (hi₀ : IsPullback i₀ fk f₀ (Spec.map (CommRingCat.ofHom ρ))) :
    Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fk.appTop).hom := by sorry
