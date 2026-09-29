-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_mul_comp_eq_mul_comp_of_one_comp_eq_one
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.mul_comp_eq_mul_comp_of_one_comp_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/15852397-f343-58ae-a413-f786f6accbf0
-- title:
--   Rigidity: unit-preserving maps of abelian schemes are homomorphisms
-- statement:
--   Let $R$ be a commutative ring, and let $f : A \to \operatorname{Spec} R$ and $g : B \to \operatorname{Spec} R$ be morphisms of schemes. Assume `AbelianSchemePropertyBundle R f`, i.e. $f$ is smooth and proper, every fibre $f^{-1}(\{s\})$ of the underlying map is connected (and nonempty), and $f$ admits at least one relative group law. Let $L$ be such a relative group law on $f$: for each $t : T \to \operatorname{Spec} R$ a group structure (multiplication, unit, inverse, with associativity, unit laws and left inverse law) on the set $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of points of $A$ over $t$, compatible with composition $\psi \circ t' = t$ in the base. Assume $g$ is separated and carries a relative group law $M$ of the same kind; no smoothness, flatness, properness or commutativity is assumed of $g$. Let $u : A \to B$ satisfy $g \circ u = f$, and suppose the unit section of $L$ at the identity of $\operatorname{Spec} R$, followed by $u$, equals the unit section of $M$ at the identity. Then for every $t : T \to \operatorname{Spec} R$ and all points $P, Q$ of $A$ over $t$, the underlying morphism of $L$-product $P \cdot Q$ followed by $u$ equals the underlying morphism of the $M$-product of $P$ followed by $u$ and $Q$ followed by $u$.
--
--   This is the rigidity statement that a morphism of pointed group schemes over an arbitrary base ring whose source is an abelian scheme and whose target is separated is automatically a homomorphism on points, here expressed functorially in terms of relative group laws. It is used in the comparison of framed polarised abelian schemes and in the construction of isomorphisms of deformations, where a map is first produced compatibly with unit sections only.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_mul_comp_eq_mul_comp_of_one_comp_eq_one.lean

import Mathlib
import Definitions.Def_JacJ1Iface

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.mul_comp_eq_mul_comp_of_one_comp_eq_one
    {R : Type u} [CommRing R] {A B : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} {g : B ⟶ Spec (CommRingCat.of R)}
    (hA : AbelianSchemePropertyBundle R f) (L : RelativeGroupLaw R f)
    [IsSeparated g] (M : RelativeGroupLaw R g)
    (u : A ⟶ B) (hu : u ≫ g = f)
    (hone : (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ u = (M.one (𝟙 (Spec (CommRingCat.of R)))).1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f) :
    (L.mul t P Q).1 ≫ u =
      (M.mul t ⟨P.1 ≫ u, by rw [Category.assoc, hu, P.2]⟩ ⟨Q.1 ≫ u, by rw [Category.assoc, hu, Q.2]⟩).1 := by sorry
