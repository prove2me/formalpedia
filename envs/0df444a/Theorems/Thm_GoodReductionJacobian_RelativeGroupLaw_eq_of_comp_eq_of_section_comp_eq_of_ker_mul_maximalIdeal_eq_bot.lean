-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_eq_of_comp_eq_of_section_comp_eq_of_ker_mul_maximalIdeal_eq_bot
-- name    : GoodReductionJacobian.RelativeGroupLaw.eq_of_comp_eq_of_section_comp_eq_of_ker_mul_maximalIdeal_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/6a26f7ca-063d-5d68-b20e-db7e20e1a83f
-- title:
--   Rigidity of two lifts agreeing on reduction and a section
-- statement:
--   Let $T'$ be an Artinian local ring whose residue field is algebraically closed, let $T$ be a commutative ring, and let $\pi : T' \to T$ be a surjective ring homomorphism whose kernel is nilpotent and satisfies $(\ker \pi)\cdot \mathfrak m_{T'} = 0$. Let $f_0 : A_0 \to \operatorname{Spec} T$ carry a relative group law $L_0$, i.e. a group structure on the sets $\{\varphi : X \to A_0 \mid \varphi \circ f_0 = t\}$ of $T$-morphisms into $A_0$, for every $t : X \to \operatorname{Spec} T$, compatible with base change along morphisms of test schemes; assume $L_0$ is commutative, and that $f_0$ is smooth, proper, with connected fibres and admits some relative group law. Let $f : A \to \operatorname{Spec} T'$ be smooth and proper, and let $g : A_0 \to A$ exhibit $(A_0, f_0)$ as the pullback of $f$ along $\operatorname{Spec} \pi$. Let $q : Y \to \operatorname{Spec} T'$ be smooth and proper with all fibres $q^{-1}(x)$ connected, let $g_Y : Y_0 \to Y$ exhibit $(Y_0, q_0)$ as the pullback of $q$ along $\operatorname{Spec} \pi$, and let $s : \operatorname{Spec} T' \to Y$ satisfy $s$ followed by $q$ equal to the identity. Then any two morphisms $u, v : Y \to A$ over $\operatorname{Spec} T'$ with $g_Y$ followed by $u$ equal to $g_Y$ followed by $v$, and $s$ followed by $u$ equal to $s$ followed by $v$, are equal.
--
--   This is the rigidity statement underlying the lifting of a group law through a small extension: a morphism from a smooth proper scheme with connected fibres into a smooth proper scheme deforming an abelian scheme is determined by its reduction together with its value on one section. It is cited in the construction of a commutative relative group law on $A$ lifting $L_0$ along $\pi$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_eq_of_comp_eq_of_section_comp_eq_of_ker_mul_maximalIdeal_eq_bot.lean

import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.eq_of_comp_eq_of_section_comp_eq_of_ker_mul_maximalIdeal_eq_bot
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T'] [IsAlgClosed (ResidueField T')]
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
