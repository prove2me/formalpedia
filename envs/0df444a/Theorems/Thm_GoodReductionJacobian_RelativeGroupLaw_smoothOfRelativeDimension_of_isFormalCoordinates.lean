-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_smoothOfRelativeDimension_of_isFormalCoordinates
-- name    : GoodReductionJacobian.RelativeGroupLaw.smoothOfRelativeDimension_of_isFormalCoordinates
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/9ff01f75-c664-5b5a-b33c-f204287326ad
-- title:
--   Formal coordinates of dimension d give relative dimension d
-- statement:
--   Let $B$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} B$ a morphism, and let $L$ be a relative group law on $f$ in the sense of the project: functorial multiplication, unit and inverse operations on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of sections of $f$ over an arbitrary $t : T \to \operatorname{Spec} B$, satisfying associativity, the unit laws, left inversion, and compatibility with precomposition by morphisms $\psi$ over $\operatorname{Spec} B$. Assume `AbelianSchemePropertyBundle B f`, i.e. $f$ is smooth and proper, every fibre $f^{-1}(s)$ is connected, and $f$ admits a relative group law. Let $d$ be a natural number and $F$ a $d$-dimensional formal group law over $B$: $d$ power series in the variables indexed by $\mathrm{Fin}\,d \sqcup \mathrm{Fin}\,d$ with vanishing constant term, linear coefficients given by the identity on each summand, and satisfying the associativity identity. Let $\theta$ assign to every $B$-algebra $B'$ and every $d$-tuple $s \in (B')^d$ a section of $f$ over $\operatorname{Spec} B' \to \operatorname{Spec} B$, and assume `L.IsFormalCoordinates F θ`: $\theta$ is compatible with $B$-algebra maps on nilpotent tuples, and for every $B$-algebra $B'$, every ideal $J$ with $J^{n+1} = 0$, the tuples with entries in $J$ are sent to points congruent to the unit modulo $J$, injectively, surjectively onto all such infinitesimal points, and with $\theta$ of the degree-$n$ truncated evaluation $F(s,t)$ equal to the $L$-product $\theta(s)\cdot\theta(t)$. Then $f$ is smooth of relative dimension $d$.
--
--   This is the passage from a formal group of dimension $d$ along the unit section of a group law to the relative dimension of the ambient smooth proper morphism, as used for Jacobians with good reduction. It is invoked in the construction of formal coordinates and of lifts of points and homomorphisms, for instance in the deformation-theoretic arguments producing liftings of infinitesimal points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_smoothOfRelativeDimension_of_isFormalCoordinates.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.smoothOfRelativeDimension_of_isFormalCoordinates
    {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)}
    (L : RelativeGroupLaw B f) (hA : AbelianSchemePropertyBundle B f)
    {d : ℕ} (F : MvFormalGroup d B) (θ : RelativeGroupLaw.FormalCoordinates f d) (hθ : L.IsFormalCoordinates F θ) :
    SmoothOfRelativeDimension d f := by sorry
