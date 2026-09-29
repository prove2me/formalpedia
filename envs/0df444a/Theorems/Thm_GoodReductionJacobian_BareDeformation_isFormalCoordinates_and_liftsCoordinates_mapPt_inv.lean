-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_isFormalCoordinates_and_liftsCoordinates_mapPt_inv
-- name    : GoodReductionJacobian.BareDeformation.isFormalCoordinates_and_liftsCoordinates_mapPt_inv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/28701d00-06f4-52e3-b6c0-964339fbb202
-- title:
--   Transport of formal coordinates along an isomorphism of bare deformations
-- statement:
--   Let $B$ and $B_1$ be commutative rings with $B_1$ a $B$-algebra, let $f_1 : A_1 \to \operatorname{Spec} B_1$ be a scheme over $B_1$ carrying a relative group law $L_1$, let $d$ be a natural number, and let $\theta_1$ be a family of formal coordinates for $f_1$ of dimension $d$, i.e. an assignment, for each $B_1$-algebra $B'$, of a point of $A_1$ over $\operatorname{Spec} B'$ to each $d$-tuple in $B'$. Let $D$ and $D'$ be bare deformations of $(f_1, L_1)$ over $B$ (each consisting of a scheme $A$ over $\operatorname{Spec} B$ with a commutative relative group law, the abelian-scheme property bundle, and a morphism $g : A_1 \to A$ making $f_1$ a pullback of $f$ along $\operatorname{Spec}$ of $B \to B_1$ and compatible with the group laws). Let $e : D.A \cong D'.A$ be an isomorphism with $e.\mathrm{hom}$ followed by $D'.f$ equal to $D.f$ and $D.g$ followed by $e.\mathrm{hom}$ equal to $D'.g$, and assume that composition with $e.\mathrm{hom}$ carries $D.L$-products of points to $D'.L$-products. Let $F'$ be a $d$-dimensional formal group law over $B$ and $\theta'$ formal coordinates for $D'.f$ such that $D'.L$ has law $F'$ in the coordinates $\theta'$ — that is, $\theta'$ is natural under $B$-algebra maps on nilpotent tuples and, for every $B$-algebra $B'$, ideal $J$ with $J^{n+1} = 0$, the points $\theta'(s)$ for $s$ with entries in $J$ are exactly the $J$-infinitesimal points (each such point is $J$-infinitesimal, distinct tuples give distinct points, every $J$-infinitesimal point arises) and $\theta'(F'.\mathrm{nilMul}\,n\,s\,t) = \theta'(s) \cdot \theta'(t)$ — and such that $\theta'$ lifts $\theta_1$, i.e. $(\theta_1(s)) \circ D'.g$ equals $\theta'(s)$ for nilpotent $s$ in any $B''$ that is an algebra over both $B$ and $B_1$ compatibly. Then the coordinates obtained by composing $\theta'$ with $e.\mathrm{inv}$ satisfy the same two properties for $D$: $D.L$ has law $F'$ in them, with the *same* $F'$, and they lift $\theta_1$ through $D.g$.
--
--   This is the transport-of-structure step showing that formal coordinates at the unit section, together with the formal group law they exhibit, are carried along a group-law isomorphism of bare deformations; it underlies the comparison of formal group laws attached to isomorphic deformations. It is used in the results on shift and regluing of tangent coordinates for bare deformations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_isFormalCoordinates_and_liftsCoordinates_mapPt_inv.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
open scoped TensorProduct

theorem GoodReductionJacobian.BareDeformation.isFormalCoordinates_and_liftsCoordinates_mapPt_inv
    (B B₁ : Type) [CommRing B] [CommRing B₁] [Algebra B B₁]
    {A₁ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)} {L₁ : RelativeGroupLaw B₁ f₁} {d : ℕ}
    (θ₁ : RelativeGroupLaw.FormalCoordinates f₁ d)
    (D D' : BareDeformation f₁ L₁ B) (e : D.A ≅ D'.A) (he : e.hom ≫ D'.f = D.f) (hg : D.g ≫ e.hom = D'.g)
    (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t D.f),
      mapPt e.hom he (D.L.mul t P Q) = D'.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q))
    (F' : MvFormalGroup d B) (θ' : RelativeGroupLaw.FormalCoordinates D'.f d)
    (hθ' : D'.L.IsFormalCoordinates F' θ') (hl' : D'.LiftsCoordinates θ₁ θ') :
    D.L.IsFormalCoordinates F'
        (fun B'' _ _ s => mapPt e.inv (by rw [← he, e.inv_hom_id_assoc]) (θ' B'' s)) ∧
      D.LiftsCoordinates θ₁ (fun B'' _ _ s => mapPt e.inv (by rw [← he, e.inv_hom_id_assoc]) (θ' B'' s)) := by sorry
