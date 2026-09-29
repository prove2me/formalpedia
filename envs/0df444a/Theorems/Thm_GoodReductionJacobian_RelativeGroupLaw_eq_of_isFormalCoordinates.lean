-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_eq_of_isFormalCoordinates
-- name    : GoodReductionJacobian.RelativeGroupLaw.eq_of_isFormalCoordinates
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/a6bdf34d-a1e3-5a8a-8da6-bf2550c5d8a3
-- title:
--   Uniqueness of the dimension of formal coordinates
-- statement:
--   Let $B$ be a nontrivial commutative ring, $A$ a scheme, and $f : A \to \operatorname{Spec} B$ a morphism, and let $L$ be a relative group law on $f$: for every $B$-scheme $t : T \to \operatorname{Spec} B$ a multiplication, unit and inverse on the set of $T$-points of $A$ over $t$ (morphisms $T \to A$ composing with $f$ to $t$), satisfying associativity, both unit laws, left inversion, and naturality of the multiplication under base change along any $\psi : T' \to T$ over $\operatorname{Spec} B$. Let $g, g'$ be natural numbers, $F$ a $g$-dimensional formal group law over $B$ and $F'$ a $g'$-dimensional one (tuples of power series in two families of variables with vanishing constant term, identity linear part in each family, and satisfying the associativity identity). Let $\theta$, resp. $\theta'$, assign to each $B$-algebra $B'$ and each tuple in $(B')^g$, resp. $(B')^{g'}$, a point of $A$ over $\operatorname{Spec} B' \to \operatorname{Spec} B$, and assume each is a system of formal coordinates for $L$ with group law $F$, resp. $F'$: compatible with $B$-algebra maps on tuples of nilpotents, and for every $B$-algebra $B'$ and ideal $J$ with $J^{n+1} = 0$, tuples with entries in $J$ give points whose reduction modulo $J$ is the unit, distinct such tuples give distinct points, every point infinitesimal with respect to $J$ arises from such a tuple, and the truncated formal multiplication of two such tuples is carried to the $L$-product of their points. Then $g = g'$.
--
--   This is the well-definedness of the dimension of the formal group attached to the unit section of a relative group law; the dimension is read off from the tangent space at the unit over a residue field of $B$. It is used to pin the dimension of the formal coordinates of a deformation, in [`GoodReductionJacobian.BareDeformation.exists_deformation_isFormalCoordinates_liftsCoordinates`](thm.html#GoodReductionJacobian.BareDeformation.exists_deformation_isFormalCoordinates_liftsCoordinates). The nontriviality of $B$ is needed: over the zero ring every $g$ would be admissible.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_eq_of_isFormalCoordinates.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.eq_of_isFormalCoordinates
    {B : Type} [CommRing B] [Nontrivial B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)}
    (L : RelativeGroupLaw B f) {g g' : ℕ} (F : MvFormalGroup g B) (F' : MvFormalGroup g' B)
    (θ : RelativeGroupLaw.FormalCoordinates f g) (θ' : RelativeGroupLaw.FormalCoordinates f g')
    (hθ : L.IsFormalCoordinates F θ) (hθ' : L.IsFormalCoordinates F' θ') : g = g' := by sorry
