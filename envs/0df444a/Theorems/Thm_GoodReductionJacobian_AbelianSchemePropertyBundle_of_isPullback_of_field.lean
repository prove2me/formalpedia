-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback_of_field
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.of_isPullback_of_field
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/a231d5ef-79d3-5893-9133-b6a1ee17c039
-- title:
--   Abelian scheme property transported along a cartesian square
-- statement:
--   Let $R$ be a commutative ring, let $A$ be a scheme and $f : A \to \operatorname{Spec} R$ a morphism satisfying the predicate `AbelianSchemePropertyBundle`, i.e. $f$ is smooth, $f$ is proper, for every point $s$ of $\operatorname{Spec} R$ the fibre $f^{-1}(\{s\})$ (preimage under the underlying map of topological spaces) is a connected nonempty set, and the set of relative group laws on $f$ is nonempty, a relative group law being a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points over $\operatorname{Spec} R$, for all schemes $T$ and all $t : T \to \operatorname{Spec} R$, with multiplication, unit and inverse satisfying associativity, the unit laws, left inverses, and naturality in $T$. Let $k$ be a field and $\varphi : R \to k$ a ring homomorphism. Let $A'$ be a scheme with morphisms $f' : A' \to \operatorname{Spec} k$ and $g : A' \to A$ forming a cartesian square: $g$ followed by $f$ equals $f'$ followed by $\operatorname{Spec}(\varphi)$, and this square is a pullback. Assume further that a relative group law $L'$ on $f'$ is given. Then $f'$ satisfies `AbelianSchemePropertyBundle` over $k$: it is smooth, proper, has connected fibres over every point of $\operatorname{Spec} k$, and admits a relative group law.
--
--   This says that the fibre of an abelian scheme over a $k$-valued point of the base, presented by an arbitrary cartesian square rather than by the literal fibre product, is again an abelian scheme over $k$ — an abelian variety, once the group law is supplied as data. It is used to provide the abelian-variety hypotheses on generic and special fibres in the good-reduction analysis of Jacobians, for instance in the specialisation of principal polarisations and in statements about kernels of polarisation maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback_of_field.lean

import Mathlib
import Definitions.Def_JacJ1Iface

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.of_isPullback_of_field
    {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (hA : AbelianSchemePropertyBundle R f)
    (k : Type) [Field k] (φ : R →+* k)
    {A' : Scheme.{0}} (f' : A' ⟶ Spec (CommRingCat.of k)) (g : A' ⟶ A)
    (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ))) (L' : RelativeGroupLaw k f') :
    AbelianSchemePropertyBundle k f' := by sorry
