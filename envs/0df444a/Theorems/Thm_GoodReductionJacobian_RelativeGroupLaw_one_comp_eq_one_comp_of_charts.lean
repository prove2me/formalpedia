-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_one_comp_eq_one_comp_of_charts
-- name    : GoodReductionJacobian.RelativeGroupLaw.one_comp_eq_one_comp_of_charts
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/cd1f3a20-c44d-5293-9e0e-b30364a96196
-- title:
--   Units of two charts agree in Y when multiplications do
-- statement:
--   Let $S$, $B_1$, $B_2$ be commutative rings with $B_1$ and $B_2$ algebras over $S$, and let $Y$, $A_1$, $A_2$ be schemes. Given $f : Y \to \operatorname{Spec} S$, a morphism $f_1 : A_1 \to \operatorname{Spec} B_1$ with $\iota_1 : A_1 \to Y$ satisfying $\iota_1$ followed by $f$ equals $f_1$ followed by $\operatorname{Spec}$ of the structure map $S \to B_1$, and a morphism $f_2 : A_2 \to \operatorname{Spec} B_2$ with a monomorphism $\iota_2 : A_2 \to Y$ such that the square with sides $\iota_2$, $f_2$, $f$ and $\operatorname{Spec}$ of $S \to B_2$ is cartesian. Suppose $L_1$, $L_2$ are relative group laws on $f_1$ over $B_1$ and on $f_2$ over $B_2$ in the sense of the project structure `RelativeGroupLaw`: functorial multiplication, unit and inverse operations on the sets $\mathrm{SchemeHomOver}\,t\,f_i$ of morphisms $T \to A_i$ composing with $f_i$ to a given $t$, subject to associativity, unit laws, left inverses and compatibility with base change along $T' \to T$. Assume the multiplications agree in $Y$: for all $T$, all $t_1 : T \to \operatorname{Spec} B_1$, $t_2 : T \to \operatorname{Spec} B_2$ and all points $a,b$ over $t_1$ and $a',b'$ over $t_2$ with $\iota_1 \circ a = \iota_2 \circ a'$ and $\iota_1 \circ b = \iota_2 \circ b'$, one has $\iota_1 \circ (a \cdot_{L_1} b) = \iota_2 \circ (a' \cdot_{L_2} b')$. Then for any $T$ and any $t_1$, $t_2$ with equal composites to $\operatorname{Spec} S$, the two units satisfy $\iota_1 \circ L_1.\mathrm{one}(t_1) = \iota_2 \circ L_2.\mathrm{one}(t_2)$.
--
--   This is the unit clause in the gluing of relative group laws given on two charts of a scheme $Y$ over a base: agreement of the multiplications inside $Y$ forces agreement of the units there. It is used in the construction of a group law on a Jacobian with good reduction from local charts, being cited by the corresponding statements for inverses and for the commutativity and multiplication-compatibility of the glued law.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_one_comp_eq_one_comp_of_charts.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.one_comp_eq_one_comp_of_charts
    {S B₁ B₂ : Type u} [CommRing S] [CommRing B₁] [CommRing B₂] [Algebra S B₁] [Algebra S B₂]
    {Y A₁ A₂ : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of S))
    (f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)) (ι₁ : A₁ ⟶ Y)
    (h₁ : ι₁ ≫ f = f₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap S B₁)))
    (f₂ : A₂ ⟶ Spec (CommRingCat.of B₂)) (ι₂ : A₂ ⟶ Y) [Mono ι₂]
    (h₂ : IsPullback ι₂ f₂ f (Spec.map (CommRingCat.ofHom (algebraMap S B₂))))
    (L₁ : RelativeGroupLaw B₁ f₁) (L₂ : RelativeGroupLaw B₂ f₂)
    (hagree : ∀ {T : Scheme.{u}} (t₁ : T ⟶ Spec (CommRingCat.of B₁)) (t₂ : T ⟶ Spec (CommRingCat.of B₂))
        (a b : SchemeHomOver t₁ f₁) (a' b' : SchemeHomOver t₂ f₂),
        a.1 ≫ ι₁ = a'.1 ≫ ι₂ → b.1 ≫ ι₁ = b'.1 ≫ ι₂ → (L₁.mul t₁ a b).1 ≫ ι₁ = (L₂.mul t₂ a' b').1 ≫ ι₂)
    {T : Scheme.{u}} (t₁ : T ⟶ Spec (CommRingCat.of B₁)) (t₂ : T ⟶ Spec (CommRingCat.of B₂))
    (ht : t₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap S B₁)) = t₂ ≫ Spec.map (CommRingCat.ofHom (algebraMap S B₂))) :
    (L₁.one t₁).1 ≫ ι₁ = (L₂.one t₂).1 ≫ ι₂ := by sorry
