-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_pullback_snd_of_isClosedImmersion_of_nsmul_eq_one
-- name    : GoodReductionJacobian.RelativeGroupLaw.formallyUnramified_pullback_snd_of_isClosedImmersion_of_nsmul_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/0ca326a9-1450-553a-9ad3-f7916ee81794
-- title:
--   Closed n-torsion subschemes formally unramified over a local base
-- statement:
--   Let $R$ and $R'$ be commutative rings with $R'$ local, and let $\iota \colon \operatorname{Spec} R' \to \operatorname{Spec} R$ be a morphism of schemes. Let $f \colon A \to \operatorname{Spec} R$ be a scheme over $\operatorname{Spec} R$ and let $G$ be a `RelativeGroupLaw` for $f$: a functorial group structure on the sets $\mathrm{SchemeHomOver}\, t\, f = \{\varphi \colon T \to A \mid \varphi \circ f = t\}$ of sections over arbitrary $t \colon T \to \operatorname{Spec} R$, given by operations `mul`, `one`, `inv` satisfying associativity, the two unit laws and left inverses, with `mul` natural under precomposition with any $\psi \colon T' \to T$ over $\operatorname{Spec} R$. Assume `hcomm`: `mul` is commutative for every $T$ and every $t$. Let $n$ be a natural number whose image in $R'$ is a unit. Let $i \colon X \to A$ be a closed immersion such that the tautological point $\langle i, \mathrm{rfl}\rangle$ of $A$ over $t = i \circ f$ is killed by $n$, i.e. the $n$-fold iterate $\mathrm{nsmul}$ (the $n$-th `mul`-power, computed by recursion from `one`) of that point equals $G.\mathrm{one}\,(i \circ f)$. Then the second projection $X \times_{\operatorname{Spec} R} \operatorname{Spec} R' \to \operatorname{Spec} R'$, that is `pullback.snd (i ≫ f) ι`, is formally unramified.
--
--   This is the standard statement that a closed subscheme of the $n$-torsion of a commutative group scheme is unramified over a base in which $n$ is invertible, in the formally unramified form and for the functorially presented group law used in this development. It is the input used to obtain étale-ness away from the relevant prime for closed subgroup schemes of torsion of Jacobians with good reduction, and is cited in the construction of quotients of fake elliptic curves and of their extra level structures.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_pullback_snd_of_isClosedImmersion_of_nsmul_eq_one.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.formallyUnramified_pullback_snd_of_isClosedImmersion_of_nsmul_eq_one
    {R : Type u} [CommRing R] {R' : Type u} [CommRing R'] [IsLocalRing R']
    (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (n : ℕ) (hn : IsUnit (n : R'))
    {X : Scheme.{u}} (i : X ⟶ A) [IsClosedImmersion i]
    (htors : G.nsmul (i ≫ f) n ⟨i, rfl⟩ = G.one (i ≫ f)) :
    FormallyUnramified (pullback.snd (i ≫ f) ι) := by sorry
