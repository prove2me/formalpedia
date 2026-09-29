-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isPullback_schemeNsmul_baseChange_and_of_isStableUnderBaseChange
-- name    : GoodReductionJacobian.RelativeGroupLaw.isPullback_schemeNsmul_baseChange_and_of_isStableUnderBaseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/ba706490-caa9-5be4-be54-53d26644d5d2
-- title:
--   Base change of [n] on a relative group law is cartesian
-- statement:
--   Let $R$ and $R'$ be commutative rings, let $\iota\colon\operatorname{Spec}R'\to\operatorname{Spec}R$ be a morphism of schemes, let $A$ be a scheme with a morphism $f\colon A\to\operatorname{Spec}R$, and let $G$ be a relative group law on $f$, that is, a rule assigning to each scheme $T$ and each $t\colon T\to\operatorname{Spec}R$ a multiplication, unit and inverse on the set $\{\varphi\colon T\to A \mid \varphi\circ f=t\}$ of $t$-points of $A$, satisfying associativity, the two unit laws and left invertibility, and compatible with precomposition by any $\psi\colon T'\to T$ with $\psi$ followed by $t$ equal to $t'$. Let $n\in\mathbb N$. Write $A'=A\times_{\operatorname{Spec}R}\operatorname{Spec}R'$, with structure morphism $\operatorname{pullback.snd}$ and with the base-changed group law `G.baseChange ι` obtained by transporting points of $A'$ over $T$ to points of $A$ over $T\to\operatorname{Spec}R'\to\operatorname{Spec}R$ along the first projection; for a relative group law, `schemeNsmul n` denotes the underlying morphism of the $n$-fold product of the identity point of $A$ (respectively of $A'$) with itself, formed by recursion on $n$ starting from the unit point. The conclusion is twofold: first, the square consisting of $\operatorname{pullback.fst}\colon A'\to A$ and $[n]_{A'}\colon A'\to A'$ exhibits $A'$ as a fibre product of $[n]_A\colon A\to A$ and $\operatorname{pullback.fst}\colon A'\to A$; second, for every morphism property $P$ of schemes which is stable under base change, $P([n]_A)$ implies $P([n]_{A'})$.
--
--   This is the statement that multiplication by $n$ on the base change of a relative group law is the base change of multiplication by $n$, in cartesian-square form, together with the resulting transfer of any base-change-stable property of morphisms (finiteness, flatness, quasi-compactness, being affine, being a closed immersion, and so on). It is used in the study of the $2$-torsion and of rigidified line bundles on the base-changed abelian scheme, for instance in the construction of polarisations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_isPullback_schemeNsmul_baseChange_and_of_isStableUnderBaseChange.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.isPullback_schemeNsmul_baseChange_and_of_isStableUnderBaseChange
    {R : Type u} [CommRing R] {R' : Type u} [CommRing R']
    (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) (n : ℕ) :
    IsPullback (pullback.fst f ι) ((G.baseChange ι).schemeNsmul n) (G.schemeNsmul n) (pullback.fst f ι) ∧
    ∀ P : MorphismProperty Scheme.{u}, P.IsStableUnderBaseChange →
      P (G.schemeNsmul n) → P ((G.baseChange ι).schemeNsmul n) := by sorry
