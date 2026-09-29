-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_mul_comp_hom_eq_of_iso
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_mul_comp_hom_eq_of_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/a9d0f388-eeeb-5320-b044-c838e7b56eba
-- title:
--   Transport of a relative group law along an isomorphism
-- statement:
--   Let $R$ be a commutative ring, let $A$ and $A'$ be schemes, and let $f : A \to \operatorname{Spec} R$ and $f' : A' \to \operatorname{Spec} R$ be morphisms. Suppose given an isomorphism $e : A \cong A'$ of schemes with $e$ followed by $f'$ equal to $f$, and a relative group law $L$ on $f$; here a `RelativeGroupLaw` on a morphism $g : X \to \operatorname{Spec} R$ consists of operations $\mathrm{mul}$, $\mathrm{one}$, $\mathrm{inv}$ on the sets $\mathrm{SchemeHomOver}\, t\, g = \{\varphi : T \to X \mid \varphi \text{ followed by } g = t\}$, for every $t : T \to \operatorname{Spec} R$, satisfying associativity, the two unit laws, left inversion, and naturality under precomposition with any $\psi : T' \to T$ over $\operatorname{Spec} R$. The conclusion asserts the existence of a relative group law $L'$ on $f'$ such that: for every $t : T \to \operatorname{Spec} R$ and all $x, y \in \mathrm{SchemeHomOver}\, t\, f$, the underlying morphism of $L'.\mathrm{mul}$ applied to $x$ followed by $e$ and $y$ followed by $e$ equals the underlying morphism of $L.\mathrm{mul}\, t\, x\, y$ followed by $e$; and for every such $t$, the underlying morphism of $L'.\mathrm{one}\, t$ equals that of $L.\mathrm{one}\, t$ followed by $e$. Thus $e$ is a homomorphism for $L$ and $L'$ on $T$-points and carries units to units; no hypotheses are imposed on $R$, $A$ or $f$.
--
--   This is transport of structure for group laws in the functor-of-points formulation: an isomorphism of schemes over $\operatorname{Spec} R$ carries a relative group law to one on the target for which it is a homomorphism. It is used to move a group law between different models of the same object, for instance between Mathlib's chosen pullback and an abstract cartesian square, and is cited in the study of the locus where geometric fibres carry a relative group law and in the fibrewise smoothness criterion for such laws.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_mul_comp_hom_eq_of_iso.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_mul_comp_hom_eq_of_iso
    {R : Type u} [CommRing R] {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    (e : A ≅ A') (he : e.hom ≫ f' = f) (L : RelativeGroupLaw R f) :
    ∃ L' : RelativeGroupLaw R f',
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
        (L'.mul t ⟨x.1 ≫ e.hom, by rw [Category.assoc, he, x.2]⟩ ⟨y.1 ≫ e.hom, by rw [Category.assoc, he, y.2]⟩).1 =
          (L.mul t x y).1 ≫ e.hom) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), (L'.one t).1 = (L.one t).1 ≫ e.hom) := by sorry
