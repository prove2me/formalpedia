-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_deformation_isFormalCoordinates_liftsCoordinates
-- name    : GoodReductionJacobian.BareDeformation.exists_deformation_isFormalCoordinates_liftsCoordinates
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/a52d8d44-34f9-5f89-b49b-01931792f63c
-- title:
--   Formal coordinates on a bare deformation lifting given ones
-- statement:
--   Let $B$ be a local ring and $B_1$ a $B$-algebra such that the structure map $B \to B_1$ is surjective with nilpotent kernel. Let $f_1 : A_1 \to \operatorname{Spec} B_1$ be a scheme over $\operatorname{Spec} B_1$ equipped with a relative group law $L_1$, that is, functorial multiplication, unit and inversion on sections of $f_1$ over arbitrary $\operatorname{Spec} B_1$-schemes satisfying the group axioms and compatible with base change. Let $\hat G_1$ be a two-dimensional formal group law over $B_1$ (two power series in two pairs of variables, with vanishing constant term, identity linear part and associative), and let $\theta_1$ assign to each $B_1$-algebra $B'$ and each pair $s$ of elements of $B'$ a section of $f_1$ over $\operatorname{Spec} B'$, in such a way that $\theta_1$ is a system of formal coordinates for $L_1$ with law $\hat G_1$: it commutes with $B_1$-algebra maps on nilpotent tuples, and for every $B_1$-algebra $B'$ and ideal $J$ with $J^{n+1} = 0$ the tuples in $J$ are carried bijectively onto the sections of $f_1$ over $\operatorname{Spec} B'$ that become the unit section modulo $J$, with $\theta_1(\hat G_1(s,t)) = L_1(\theta_1(s), \theta_1(t))$ for such tuples, the formal group law being evaluated by nilpotent truncation. Let $D$ be a bare deformation of $(f_1, L_1)$ to $B$: a scheme $D.A$ over $\operatorname{Spec} B$ with a commutative relative group law $D.L$, whose structure morphism is smooth and proper with connected fibres and admits a relative group law, together with a morphism $D.g : A_1 \to D.A$ exhibiting $f_1$ as the pullback of $D.f$ along $\operatorname{Spec} B_1 \to \operatorname{Spec} B$ and compatible with the two multiplications. The conclusion is that there exist a deformation $G$ of $\hat G_1$ to $B$, that is, a two-dimensional formal group law $G.F$ over $B$ whose coefficientwise image under $B \to B_1$ equals $\hat G_1$ on the nose, and a system of formal coordinates $\theta$ in dimension $2$ for $D.f$, such that $G.F$ is commutative, $\theta$ is a system of formal coordinates for $D.L$ with law $G.F$, and $\theta$ lifts $\theta_1$ in the sense that for every ring $B''$ that is simultaneously a $B$-algebra and a $B_1$-algebra compatibly, and every pair $s$ of nilpotent elements of $B''$, the section $\theta_1(s)$ followed by $D.g$ equals the section $\theta(s)$.
--
--   This is the Serre–Tate style statement that a bare deformation of a group-law-carrying scheme over $B_1$ to a local ring $B$ with nilpotent augmentation ideal carries a formal group law over $B$ reducing exactly to the given one, in coordinates lifting the given coordinates. It feeds the further analysis of such deformations over rings with $(\ker) \cdot \mathfrak{m} = 0$, the construction of the associated linear map on point derivations, and the comparison of shifts of regluing data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_exists_deformation_isFormalCoordinates_liftsCoordinates.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_MvFormalGroup_Deformation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld IsLocalRing
open scoped TensorProduct

theorem GoodReductionJacobian.BareDeformation.exists_deformation_isFormalCoordinates_liftsCoordinates
    (B B₁ : Type) [CommRing B] [IsLocalRing B] [CommRing B₁] [Algebra B B₁]
    (hπ : Function.Surjective (algebraMap B B₁)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₁)))
    {A₁ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)} {L₁ : RelativeGroupLaw B₁ f₁}
    (Ĝ₁ : MvFormalGroup 2 B₁) (θ₁ : RelativeGroupLaw.FormalCoordinates f₁ 2) (hθ₁ : L₁.IsFormalCoordinates Ĝ₁ θ₁)
    (D : BareDeformation f₁ L₁ B) :
    ∃ (G : MvFormalGroup.Deformation Ĝ₁ B) (θ : RelativeGroupLaw.FormalCoordinates D.f 2),
      G.F.IsComm ∧ D.L.IsFormalCoordinates G.F θ ∧ D.LiftsCoordinates θ₁ θ := by sorry
