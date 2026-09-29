-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isFormalCoordinates_of_isLocalRing
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_isFormalCoordinates_of_isLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/6fbc1fdc-b436-5003-8fc0-81f07b67ec17
-- title:
--   Formal coordinates for a smooth commutative relative group law over a local base
-- statement:
--   Let $B$ be a commutative local ring, $A$ a scheme, and $f : A \to \operatorname{Spec} B$ a morphism of schemes. Let $L$ be a relative group law on $f$ over $B$: for each $B$-scheme $t : T \to \operatorname{Spec} B$ a multiplication, a unit and an inversion on the set of sections $\{\varphi : T \to A \mid \varphi \text{ followed by } f = t\}$, satisfying associativity, both unit laws and left inverse, and compatible with base change along any $\psi : T' \to T$ with $\psi$ followed by $t$ equal to $t'$. Assume $L$ is commutative, i.e. its multiplication is commutative on the sections over every $T$, and that $f$ is smooth. Then there exist an integer $g$, a $g$-dimensional formal group law $F$ over $B$ (a $g$-tuple of power series in variables indexed by $\mathrm{Fin}\,g \oplus \mathrm{Fin}\,g$, with vanishing constant term, with the linear coefficient of $X_{\mathrm{inl}\,j}$ and of $X_{\mathrm{inr}\,j}$ in the $i$-th component equal to $\delta_{ij}$, and satisfying the associativity identity under substitution), and a family $\theta$ assigning to every $B$-algebra $B'$ and every $s \in (B')^g$ a section of $f$ over $\operatorname{Spec} B' \to \operatorname{Spec} B$, such that: $F$ is commutative (substituting the two blocks of variables for one another fixes each component of $F$), and $(F,\theta)$ are formal coordinates for $L$, namely (i) for every $B$-algebra map $\varphi : B' \to B''$ and every tuple $s$ of nilpotent elements of $B'$, $\theta_{B''}(\varphi \circ s)$ is the base change of $\theta_{B'}(s)$ along $\operatorname{Spec}\varphi$; and (ii) for every $B$-algebra $B'$, every ideal $J \subseteq B'$ and every $n$ with $J^{n+1} = 0$: tuples $s$ with all $s_i \in J$ give sections that are $J$-infinitesimal (their restriction along $\operatorname{Spec}(B'/J) \to \operatorname{Spec} B'$ is the unit section of $L$ over $\operatorname{Spec}(B'/J)$), $\theta_{B'}$ is injective on such tuples, every $J$-infinitesimal section of $f$ over $\operatorname{Spec} B'$ is $\theta_{B'}(s)$ for some such $s$, and $\theta_{B'}$ carries the truncated evaluation of $F$ at level $n$ on two such tuples $s,t$ to the $L$-product of $\theta_{B'}(s)$ and $\theta_{B'}(t)$.
--
--   This is the existence of the formal group along the unit section of a smooth commutative relative group law, in the form of coordinates $\theta$ valid over the whole local base $B$ rather than only Zariski-locally on $\operatorname{Spec} B$. It is used for the deformation-theoretic statement [`GoodReductionJacobian.BareDeformation.exists_deformation_isFormalCoordinates_liftsCoordinates`](thm.html#GoodReductionJacobian.BareDeformation.exists_deformation_isFormalCoordinates_liftsCoordinates) and for the comparison of two systems of formal coordinates over a field in [`GoodReductionJacobian.RelativeGroupLaw.exists_isFormalCoordinates_two_isLawHom_germ_of_abelianSchemePropertyBundle_of_field`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_isFormalCoordinates_two_isLawHom_germ_of_abelianSchemePropertyBundle_of_field).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isFormalCoordinates_of_isLocalRing.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_isFormalCoordinates_of_isLocalRing
    {B : Type} [CommRing B] [IsLocalRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)}
    (L : RelativeGroupLaw B f) (hL : L.IsCommutative) (hf : Smooth f) :
    ∃ (g : ℕ) (F : MvFormalGroup g B) (θ : RelativeGroupLaw.FormalCoordinates f g),
      F.IsComm ∧ L.IsFormalCoordinates F θ := by sorry
