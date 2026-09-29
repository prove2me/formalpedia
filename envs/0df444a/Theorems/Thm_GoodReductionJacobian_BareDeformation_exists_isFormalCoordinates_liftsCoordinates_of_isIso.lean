-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_isFormalCoordinates_liftsCoordinates_of_isIso
-- name    : GoodReductionJacobian.BareDeformation.exists_isFormalCoordinates_liftsCoordinates_of_isIso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/bda78dcf-bdfd-5037-931f-c4540414d248
-- title:
--   Re-coordinatising a group law by a strict isomorphism
-- statement:
--   Let $B \to B_1$ be a ring map, let $f_1 : A_1 \to \operatorname{Spec} B_1$ carry a relative group law $L_1$, let $\hat G_1$ be a two-dimensional formal group law over $B_1$ and $\theta_1$ a system of formal coordinates for $f_1$ in dimension $2$, i.e. an assignment, to each $B_1$-algebra $B'$ and each pair $s \in (B')^2$, of a section of $f_1$ over $\operatorname{Spec} B'$. Let $D$ be a bare deformation of $(f_1, L_1)$ to $B$: a scheme $D.A$ over $\operatorname{Spec} B$ with a commutative relative group law $D.L$, an abelian-scheme property bundle, and a morphism $D.g : A_1 \to D.A$ exhibiting $f_1$ as the pullback of $D.f$ along $\operatorname{Spec} B_1 \to \operatorname{Spec} B$ and compatible with the two multiplications. Let $G, G'$ be deformations of $\hat G_1$ over $B$, i.e. two-dimensional formal group laws over $B$ whose base change along $B \to B_1$ is $\hat G_1$, and let $\theta$ be formal coordinates for $D.f$ in dimension $2$ such that: (i) $\theta$ presents $D.L$ in the law $G.F$, meaning $\theta$ commutes with $B$-algebra maps applied to nilpotent tuples, and for every $B$-algebra $B'$, ideal $J$ with $J^{n+1} = 0$, tuples with entries in $J$ are sent to points that become the unit section modulo $J$, $\theta$ is injective on such tuples and surjective onto the $J$-infinitesimal points, and $\theta(G.F\text{-multiplication of } s,t \text{ truncated at level } n) = D.L.\mathrm{mul}(\theta s, \theta t)$; (ii) $\theta$ lifts $\theta_1$, meaning that for every $B''$ that is an algebra over both $B$ and $B_1$ in a scalar tower and every nilpotent tuple $s$ over $B''$, the section $\theta_1(s)$ followed by $D.g$ equals $\theta(s)$. Assume finally that $G$ and $G'$ are isomorphic as deformations: there is a homomorphism $G.F \to G'.F$ with a two-sided inverse whose component power series reduce to the coordinates $X_i$ over $B_1$. Then there exist formal coordinates $\theta'$ for $D.f$ in dimension $2$ which present $D.L$ in the law $G'.F$ and which likewise lift $\theta_1$ through $D.g$.
--
--   This is the change-of-coordinates step for formal group laws: a strict isomorphism between two deformations of $\hat G_1$ may be absorbed into the choice of formal parameters along the unit section, without disturbing the compatibility with the coordinates already fixed over $B_1$. It is used in the comparison of deformations of the group law with deformations of the scheme, namely by [`GoodReductionJacobian.BareDeformation.exists_isFormalCoordinates_liftsCoordinates_of_ker_mul_maximalIdeal_eq_bot`](thm.html#GoodReductionJacobian.BareDeformation.exists_isFormalCoordinates_liftsCoordinates_of_ker_mul_maximalIdeal_eq_bot).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_exists_isFormalCoordinates_liftsCoordinates_of_isIso.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_MvFormalGroup_Deformation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld IsLocalRing
open scoped TensorProduct

theorem GoodReductionJacobian.BareDeformation.exists_isFormalCoordinates_liftsCoordinates_of_isIso
    (B B₁ : Type) [CommRing B] [CommRing B₁] [Algebra B B₁]
    {A₁ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)} {L₁ : RelativeGroupLaw B₁ f₁}
    (Ĝ₁ : MvFormalGroup 2 B₁) (θ₁ : RelativeGroupLaw.FormalCoordinates f₁ 2)
    (D : BareDeformation f₁ L₁ B) (G G' : MvFormalGroup.Deformation Ĝ₁ B)
    (θ : RelativeGroupLaw.FormalCoordinates D.f 2)
    (hθ : D.L.IsFormalCoordinates G.F θ) (hl : D.LiftsCoordinates θ₁ θ) (hiso : G.IsIso G') :
    ∃ θ' : RelativeGroupLaw.FormalCoordinates D.f 2, D.L.IsFormalCoordinates G'.F θ' ∧ D.LiftsCoordinates θ₁ θ' := by sorry
