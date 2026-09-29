-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_eq_of_comp_eq_of_section_comp_eq_of_ker_mul_maximalIdeal_eq_bot_anyResidueField
-- name    : GoodReductionJacobian.RelativeGroupLaw.eq_of_comp_eq_of_section_comp_eq_of_ker_mul_maximalIdeal_eq_bot_anyResidueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/7bec132d-913b-50e4-b323-94319c6b95c5
-- title:
--   Infinitesimal rigidity of morphisms into an abelian scheme
-- statement:
--   Let $T'$ be an Artinian local commutative ring and $T$ a commutative ring, and let $\pi : T' \to T$ be a surjective ring homomorphism whose kernel is a nilpotent ideal and satisfies $(\ker \pi)\cdot \mathfrak m_{T'} = 0$, i.e. $\pi$ is a small extension. Let $f_0 : A_0 \to \operatorname{Spec} T$ be a morphism of schemes equipped with a relative group law $L_0$ over $T$ — a group structure on the set of $T$-morphisms $\{\varphi : Z \to A_0 \mid \varphi \circ f_0 = t\}$ for every $t : Z \to \operatorname{Spec} T$, compatible with base change along morphisms over $\operatorname{Spec} T$ — which is assumed commutative, and suppose $f_0$ satisfies `AbelianSchemePropertyBundle`: it is smooth and proper, each set-theoretic fibre $f_0^{-1}(s)$ is connected, and a relative group law on $f_0$ exists. Let $f : A \to \operatorname{Spec} T'$ be smooth and proper, and let $g : A_0 \to A$ exhibit $f_0$ as the base change of $f$ along $\operatorname{Spec}(\pi)$, the square being a pullback. Let $q : Y \to \operatorname{Spec} T'$ be smooth and proper with all set-theoretic fibres $q^{-1}(x)$ connected, let $q_0 : Y_0 \to \operatorname{Spec} T$ together with $g_Y : Y_0 \to Y$ be the base change of $q$ along $\operatorname{Spec}(\pi)$, again as a pullback square, and let $s$ be a section of $q$, i.e. a morphism $\operatorname{Spec} T' \to Y$ with $s \circ q$ the identity. Then any two morphisms $u, v : Y \to A$ over $\operatorname{Spec} T'$ (so $f \circ u = q = f \circ v$) which agree after restriction to $Y_0$, in that $u \circ g_Y = v \circ g_Y$, and agree along the section, in that $u \circ s = v \circ s$, are equal.
--
--   This is the infinitesimal form of the rigidity lemma for abelian schemes: a deformation of a morphism into an abelian scheme across a small extension of Artinian local base rings is determined by its value along a section. It is used in the construction of the group law on a smooth proper model of a Jacobian by successive lifting along small extensions, being cited by [`GoodReductionJacobian.RelativeGroupLaw.exists_isCommutative_comp_eq_mul_of_smallExtension`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_isCommutative_comp_eq_mul_of_smallExtension); no algebraic closedness of the residue field of $T'$ is assumed, geometric connectedness of the special fibre being supplied instead by the section $s$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_eq_of_comp_eq_of_section_comp_eq_of_ker_mul_maximalIdeal_eq_bot_anyResidueField.lean

import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.eq_of_comp_eq_of_section_comp_eq_of_ker_mul_maximalIdeal_eq_bot_anyResidueField
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    (hsmall : RingHom.ker π * maximalIdeal T' = ⊥)
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) (L₀ : RelativeGroupLaw T f₀) (hc₀ : L₀.IsCommutative)
    (h₀ : AbelianSchemePropertyBundle T f₀)
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of T')) (hs : Smooth f) (hp : IsProper f)
    (g : A₀ ⟶ A) (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom π)))
    {Y Y₀ : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of T')) (hq : Smooth q) (hqp : IsProper q)
    (hconn : ∀ x : Spec (CommRingCat.of T'), _root_.IsConnected (q.base ⁻¹' {x}))
    (q₀ : Y₀ ⟶ Spec (CommRingCat.of T)) (gY : Y₀ ⟶ Y) (hgY : IsPullback gY q₀ q (Spec.map (CommRingCat.ofHom π)))
    (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of T'))) q)
    (u v : SchemeHomOver q f) (hred : gY ≫ u.1 = gY ≫ v.1) (hsec : s.1 ≫ u.1 = s.1 ≫ v.1) :
    u = v := by sorry
