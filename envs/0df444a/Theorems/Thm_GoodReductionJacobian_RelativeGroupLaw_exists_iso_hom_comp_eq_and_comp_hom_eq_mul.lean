-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_iso_hom_comp_eq_and_comp_hom_eq_mul
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_iso_hom_comp_eq_and_comp_hom_eq_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/5979af6c-0e85-5e36-8158-31d769abb02e
-- title:
--   Translation by a section is an automorphism over the base
-- statement:
--   Let $R$ be a commutative ring, $A$ a scheme and $f \colon A \to \operatorname{Spec} R$ a morphism, and let $L$ be a relative group law on $f$ in the sense of the project, i.e. for every scheme $T$ and every $t \colon T \to \operatorname{Spec} R$ a multiplication, unit and inversion on the set $\{\varphi \colon T \to A \mid \varphi \text{ followed by } f = t\}$ of sections of $f$ over $t$, subject to associativity, the two unit laws, cancellation of a left inverse, and naturality of the multiplication under precomposition with any $\psi \colon T' \to T$ satisfying $\psi$ followed by $t$ equals $t'$. Let $d$ be such a section over $t = \mathbf{1}_{\operatorname{Spec} R}$, that is a morphism $d \colon \operatorname{Spec} R \to A$ with $d$ followed by $f$ the identity. Then there exists an isomorphism $\tau \colon A \cong A$ such that $\tau$ followed by $f$ is $f$, $\tau^{-1}$ followed by $f$ is $f$, and for every scheme $T$, every $t \colon T \to \operatorname{Spec} R$ and every section $x$ of $f$ over $t$: the composite $x$ followed by $\tau$ is the underlying morphism of $L.\mathrm{mul}\,t\,x\,d_T$, and $x$ followed by $\tau^{-1}$ is the underlying morphism of $L.\mathrm{mul}\,t\,x\,(L.\mathrm{inv}\,t\,d_T)$, where $d_T$ denotes the section $t$ followed by $d$ over $t$.
--
--   This is the statement that right translation by a section of $f$ is an automorphism of $A$ over $\operatorname{Spec} R$, in the functor-of-points formulation of a group law on $f$. It is used in the construction of Néron models by gluing translates, where charts are identified along translations by sections, and is cited in the analysis of the group law of the good-reduction Jacobian (closedness of images and ranges of monomorphic sections) and in the gluing construction for the Néron object attached to $J_0(N)$ at a prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_iso_hom_comp_eq_and_comp_hom_eq_mul.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_iso_hom_comp_eq_and_comp_hom_eq_mul
    (R : Type u) [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : GoodReductionJacobian.RelativeGroupLaw R f)
    (d : NeronModelInfra.SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    ∃ τ : A ≅ A, τ.hom ≫ f = f ∧ τ.inv ≫ f = f ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : NeronModelInfra.SchemeHomOver t f),
        x.1 ≫ τ.hom = (L.mul t x (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) d)).1) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : NeronModelInfra.SchemeHomOver t f),
        x.1 ≫ τ.inv = (L.mul t x (L.inv t (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) d))).1) := by sorry
