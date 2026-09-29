-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_inv_comp_eq_inv_comp_of_charts
-- name    : GoodReductionJacobian.RelativeGroupLaw.inv_comp_eq_inv_comp_of_charts
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/ff887ef1-4053-5935-8297-5ec611f367a6
-- title:
--   Chart inverses agree in Y when multiplications do
-- statement:
--   Let $S$, $B_1$, $B_2$ be commutative rings with $B_1$, $B_2$ algebras over $S$, and let $Y$, $A_1$, $A_2$ be schemes. Fix $f : Y \to \operatorname{Spec} S$, a morphism $f_1 : A_1 \to \operatorname{Spec} B_1$ and $\iota_1 : A_1 \to Y$ with $\iota_1$ followed by $f$ equal to $f_1$ followed by $\operatorname{Spec}$ of the structure map $S \to B_1$, and a morphism $f_2 : A_2 \to \operatorname{Spec} B_2$ together with a monomorphism $\iota_2 : A_2 \to Y$ such that the square with sides $\iota_2$, $f_2$, $f$ and $\operatorname{Spec}$ of $S \to B_2$ is cartesian. Let $L_1$ be a relative group law for $f_1$ over $B_1$ and $L_2$ one for $f_2$ over $B_2$; such a datum consists of multiplication, unit and inverse operations on the sets of sections $\{\varphi : T \to A_i \mid \varphi \text{ followed by } f_i = t\}$, functorially in a base morphism $t : T \to \operatorname{Spec} B_i$, satisfying associativity, the two unit laws, left inversion, and naturality of multiplication under precomposition by $\psi : T' \to T$ over the base. Assume that the two multiplications agree in $Y$: for all test schemes $T$, all $t_1 : T \to \operatorname{Spec} B_1$, $t_2 : T \to \operatorname{Spec} B_2$, all sections $a, b$ of $f_1$ over $t_1$ and $a', b'$ of $f_2$ over $t_2$, if $a$ followed by $\iota_1$ equals $a'$ followed by $\iota_2$ and likewise for $b, b'$, then $L_1.\mathrm{mul}\,t_1\,a\,b$ followed by $\iota_1$ equals $L_2.\mathrm{mul}\,t_2\,a'\,b'$ followed by $\iota_2$. Then for any $T$ with base morphisms $t_1, t_2$ inducing the same morphism $T \to \operatorname{Spec} S$, and any sections $x$ of $f_1$ over $t_1$ and $x'$ of $f_2$ over $t_2$ having the same image in $Y$, the inverses $L_1.\mathrm{inv}\,t_1\,x$ and $L_2.\mathrm{inv}\,t_2\,x'$ also have the same image in $Y$, i.e. the former followed by $\iota_1$ equals the latter followed by $\iota_2$.
--
--   This is the inverse clause in the gluing of relative group laws given on two charts of a scheme $Y$: once the multiplications agree on points of $Y$, the units and inverses agree automatically, so that the chartwise laws patch. It is used in the construction of a commutative group law on the ambient scheme, namely by [`GoodReductionJacobian.RelativeGroupLaw.exists_isCommutative_forall_mul_comp_eq_of_charts`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_isCommutative_forall_mul_comp_eq_of_charts).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_inv_comp_eq_inv_comp_of_charts.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.inv_comp_eq_inv_comp_of_charts
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
    (ht : t₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap S B₁)) = t₂ ≫ Spec.map (CommRingCat.ofHom (algebraMap S B₂)))
    (x : SchemeHomOver t₁ f₁) (x' : SchemeHomOver t₂ f₂) (hx : x.1 ≫ ι₁ = x'.1 ≫ ι₂) :
    (L₁.inv t₁ x).1 ≫ ι₁ = (L₂.inv t₂ x').1 ≫ ι₂ := by sorry
