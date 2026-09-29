-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isComm_of_isFormalCoordinates_of_isCommutative
-- name    : GoodReductionJacobian.RelativeGroupLaw.isComm_of_isFormalCoordinates_of_isCommutative
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/3fa7576e-2d6e-543a-8609-15cb1fdce0ac
-- title:
--   Commutativity of the formal group of a commutative relative group law
-- statement:
--   Let $B$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} B$ a morphism, and let $L$ be a relative group law on $f$: for every scheme $T$ and every morphism $t : T \to \operatorname{Spec} B$ a multiplication, unit and inversion on the set of pairs $(\varphi : T \to A)$ with $\varphi$ followed by $f$ equal to $t$, satisfying associativity, the two unit laws, left inverses, and compatibility with base change along any $\psi : T' \to T$ with $\psi$ followed by $t$ equal to $t'$. Assume $L$ is commutative, i.e. $\mathrm{mul}\,t\,x\,y = \mathrm{mul}\,t\,y\,x$ for all such $t$ and all sections $x,y$. Let $g \in \mathbb{N}$ and let $F$ be a $g$-dimensional formal group law over $B$: a family $F_i$, $i \in \mathrm{Fin}\,g$, of power series in the variables indexed by $\mathrm{Fin}\,g \sqcup \mathrm{Fin}\,g$ with vanishing constant term, with the coefficient of each degree-one variable $X_{\mathrm{inl}\,j}$ and $X_{\mathrm{inr}\,j}$ equal to $\delta_{ij}$, and satisfying the associativity identity. Let $\theta$ assign to every $B$-algebra $B'$ and every tuple $s : \mathrm{Fin}\,g \to B'$ a section of $f$ over $\operatorname{Spec} B' \to \operatorname{Spec} B$, and assume $\theta$ is a system of formal coordinates for $L$ with respect to $F$: (i) for every $B$-algebra map $\varphi : B' \to B''$ and every tuple $s$ of nilpotent elements, $\theta_{B''}(\varphi \circ s)$ is the base change of $\theta_{B'}(s)$ along $\operatorname{Spec}\varphi$; and (ii) for every $B$-algebra $B'$, every ideal $J \subseteq B'$ and every $n$ with $J^{n+1} = 0$: tuples with entries in $J$ are sent to sections that become the unit section after reduction modulo $J$, $\theta_{B'}$ is injective on such tuples, every section that becomes the unit section modulo $J$ is $\theta_{B'}(s)$ for some tuple $s$ with entries in $J$, and $\theta_{B'}$ of the degree-$n$ truncated evaluation of $F$ at $(s,t)$ equals the $L$-product of $\theta_{B'}(s)$ and $\theta_{B'}(t)$. Then $F$ is commutative: for each $i$, substituting $X_{\mathrm{inr}\,j}$ for $X_{\mathrm{inl}\,j}$ and $X_{\mathrm{inl}\,j}$ for $X_{\mathrm{inr}\,j}$ in $F_i$ returns $F_i$.
--
--   This is the classical fact that the formal group attached to a commutative group law along its unit section is a commutative formal group law, here in the relative setting of a group law on $f : A \to \operatorname{Spec} B$ read off in formal coordinates. It feeds the construction of deformations carrying formal coordinates for the Jacobian of a curve with good reduction, via [`GoodReductionJacobian.BareDeformation.exists_deformation_isFormalCoordinates_liftsCoordinates`](thm.html#GoodReductionJacobian.BareDeformation.exists_deformation_isFormalCoordinates_liftsCoordinates).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_isComm_of_isFormalCoordinates_of_isCommutative.lean

import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.isComm_of_isFormalCoordinates_of_isCommutative
    {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)}
    (L : RelativeGroupLaw B f) (hL : L.IsCommutative) {g : ℕ} (F : MvFormalGroup g B)
    (θ : RelativeGroupLaw.FormalCoordinates f g) (hθ : L.IsFormalCoordinates F θ) : F.IsComm := by sorry
