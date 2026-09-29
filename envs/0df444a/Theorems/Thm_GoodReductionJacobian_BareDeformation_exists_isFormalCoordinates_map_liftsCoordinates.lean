-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_isFormalCoordinates_map_liftsCoordinates
-- name    : GoodReductionJacobian.BareDeformation.exists_isFormalCoordinates_map_liftsCoordinates
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/0a4b0d87-2bd2-514d-a157-a5af14714973
-- title:
--   Formal coordinates transfer to the fibre of a bare deformation
-- statement:
--   Let $B$ and $B_1$ be commutative rings with $B_1$ a $B$-algebra, let $A_1$ be a scheme, $f_1 : A_1 \to \operatorname{Spec} B_1$ a morphism and $L_1$ a relative group law on $f_1$ over $B_1$ (functorial multiplication, unit and inverse on $B_1$-points, with associativity, unit, inverse and base-change naturality axioms). Let $D$ be a `BareDeformation` of $f_1$ and $L_1$ to $B$: a scheme $D.A$ with $D.f : D.A \to \operatorname{Spec} B$, a commutative relative group law $D.L$ on $D.f$, smoothness, properness, connected fibres and nonemptiness of the group-law type for $D.f$, a morphism $D.g : A_1 \to D.A$ making the square with $f_1$, $D.f$ and $\operatorname{Spec}(B_1) \to \operatorname{Spec}(B)$ a pullback, and compatibility of $L_1$-multiplication with $D.L$-multiplication after composing points with $D.g$. Let $F$ be a $g$-dimensional commutative formal group law over $B$ in the sense of [`MvFormalGroup`](def/MvFormalGroup_BasicV2.html#L15) ($g$ power series in $2g$ variables with vanishing constant terms, identity linear terms and the associativity identity), and let $\theta$ be a system of formal coordinates for $D.f$, i.e. for every $B$-algebra $B'$ a map from $g$-tuples in $B'$ to points $\operatorname{Spec} B' \to D.A$ over $\operatorname{Spec} B$, which `IsFormalCoordinates` for $D.L$ and $F$: it is natural in $B$-algebra maps on nilpotent tuples, and for every $B$-algebra $B'$ and ideal $J$ with $J^{n+1}=0$ it carries $J$-tuples injectively onto exactly those points whose reduction modulo $J$ is the unit section, and converts the truncated evaluation of $F$ at level $n$ into $D.L$-multiplication. Then there exists a system of formal coordinates $\theta_1$ for $f_1$ which `IsFormalCoordinates` for $L_1$ and the base change $F \otimes_B B_1$ (coefficients pushed forward along $B \to B_1$), and which `LiftsCoordinates` to $\theta$: for every ring $B''$ that is simultaneously a $B$- and a $B_1$-algebra compatibly, and every tuple $s$ of nilpotent elements of $B''$, the point $\theta_1(s)$ followed by $D.g$ equals $\theta(s)$.
--
--   This is the descent of formal parameters at the unit section through the cartesian square defining a bare deformation: coordinates on the deformation over $B$ induce coordinates on the given group law over $B_1$, with the reduced formal group law as multiplication law. It is used in the construction of a bare deformation together with formal coordinates, [`GoodReductionJacobian.BareDeformation.exists_deformation_isFormalCoordinates_liftsCoordinates`](thm.html#GoodReductionJacobian.BareDeformation.exists_deformation_isFormalCoordinates_liftsCoordinates).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_exists_isFormalCoordinates_map_liftsCoordinates.lean

import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.BareDeformation.exists_isFormalCoordinates_map_liftsCoordinates
    (B B₁ : Type) [CommRing B] [CommRing B₁] [Algebra B B₁]
    {A₁ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)} {L₁ : RelativeGroupLaw B₁ f₁}
    (D : BareDeformation f₁ L₁ B) {g : ℕ} (F : MvFormalGroup g B)
    (θ : RelativeGroupLaw.FormalCoordinates D.f g) (hθ : D.L.IsFormalCoordinates F θ) :
    ∃ θ₁ : RelativeGroupLaw.FormalCoordinates f₁ g,
      L₁.IsFormalCoordinates (F.map (algebraMap B B₁)) θ₁ ∧ D.LiftsCoordinates θ₁ θ := by sorry
