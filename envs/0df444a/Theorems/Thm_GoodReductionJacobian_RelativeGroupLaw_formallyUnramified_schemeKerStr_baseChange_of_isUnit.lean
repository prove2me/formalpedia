-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_schemeKerStr_baseChange_of_isUnit
-- name    : GoodReductionJacobian.RelativeGroupLaw.formallyUnramified_schemeKerStr_baseChange_of_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/cbed0957-1aac-5873-89f9-1a88108e4ca5
-- title:
--   Formal unramifiedness of the n-torsion of a base-changed group law
-- statement:
--   Let $R$ and $R'$ be commutative rings with $R'$ local, let $\iota\colon\operatorname{Spec}R'\to\operatorname{Spec}R$ be a morphism of affine schemes, let $A$ be a scheme and $f\colon A\to\operatorname{Spec}R$ a morphism, and let $G$ be a relative group law on $f$: that is, for every scheme $T$ and every $t\colon T\to\operatorname{Spec}R$ a multiplication, unit and inversion on the set of $T$-points $\{\varphi\colon T\to A \mid \varphi \text{ followed by } f = t\}$, satisfying associativity, the two unit laws, left inversion, and compatibility with composition by any $\psi\colon T'\to T$ over the base. Assume $G$ is commutative, in the sense that $G.\mathrm{mul}\,t\,x\,y = G.\mathrm{mul}\,t\,y\,x$ for all $T$, all $t$ and all points $x,y$. Let $n$ be a natural number whose image in $R'$ is a unit. Form the base-changed law `G.baseChange ι` on the structure morphism $\operatorname{pullback.snd} f\,\iota\colon A\times_{\operatorname{Spec}R}\operatorname{Spec}R'\to\operatorname{Spec}R'$, whose operations are obtained by transporting points through the pullback, and let $[n]$ be the endomorphism of $A\times_{\operatorname{Spec}R}\operatorname{Spec}R'$ given by $n$-fold multiplication applied to the identity point. The conclusion is that the second projection of the pullback of $[n]$ along the unit section $\operatorname{Spec}R'\to A\times_{\operatorname{Spec}R}\operatorname{Spec}R'$, i.e. the structure morphism of the $n$-torsion subscheme over $\operatorname{Spec}R'$, is formally unramified.
--
--   This is the statement that the kernel of multiplication by $n$ on a commutative relative group scheme is formally unramified over a local base in which $n$ is invertible, in the base-changed form (the group law lives over $R$, the local base $R'$ enters through $\iota$); the typical application takes $R=\mathbb{Z}$, $R'$ a localisation in which the relevant torsion order is invertible. It is used in the analysis of torsion on Néron models of Jacobians of modular curves, and is cited by [`GoodReductionJacobian.RelativeGroupLaw.formallyUnramified_pullback_snd_of_isClosedImmersion_of_nsmul_eq_one`](thm.html#GoodReductionJacobian.RelativeGroupLaw.formallyUnramified_pullback_snd_of_isClosedImmersion_of_nsmul_eq_one) and by [`ModularCurve.JZeroNeronObjectAtP.schemeKerStr_baseChange_props`](thm.html#ModularCurve.JZeroNeronObjectAtP.schemeKerStr_baseChange_props).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_schemeKerStr_baseChange_of_isUnit.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.formallyUnramified_schemeKerStr_baseChange_of_isUnit
    {R : Type u} [CommRing R] {R' : Type u} [CommRing R'] [IsLocalRing R']
    (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (n : ℕ) (hn : IsUnit (n : R')) :
    FormallyUnramified ((G.baseChange ι).schemeKerStr n) := by sorry
