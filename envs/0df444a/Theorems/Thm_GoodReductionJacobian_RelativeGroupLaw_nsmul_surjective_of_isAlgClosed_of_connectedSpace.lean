-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_nsmul_surjective_of_isAlgClosed_of_connectedSpace
-- name    : GoodReductionJacobian.RelativeGroupLaw.nsmul_surjective_of_isAlgClosed_of_connectedSpace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/983d0b2e-eefc-57a6-8bda-b6d2d8b733a4
-- title:
--   Multiplication by n is surjective on K-points
-- statement:
--   Let $K$ be an algebraically closed field, let $A$ be a scheme and let $f : A \to \operatorname{Spec} K$ be a smooth morphism whose source $A$ is a connected topological space. Let $G$ be a relative group law on $f$ over $K$: for every scheme $T$ and every morphism $t : T \to \operatorname{Spec} K$ it provides a multiplication, a unit and an inverse on the set of $T$-points of $A$ over $t$ (morphisms $\varphi : T \to A$ with $\varphi$ followed by $f$ equal to $t$), satisfying associativity, the two unit laws and left inversion, and such that multiplication commutes with base change along any $\psi : T' \to T$ with $\psi$ followed by $t$ equal to $t'$. Assume in addition that $G$ is commutative, i.e. $G.\mathrm{mul}\,t\,x\,y = G.\mathrm{mul}\,t\,y\,x$ for all $t$ and all points $x, y$ over $t$. Let $n$ be a natural number whose image in $K$ is a unit. Then the $n$-fold multiplication map $x \mapsto G.\mathrm{nsmul}$ at level $n$, defined by recursion from the unit by repeated multiplication by $x$, is surjective on the set of points over the identity of $\operatorname{Spec} K$, that is on the sections of $f$: every section is an $n$-th multiple of a section.
--
--   This is the field case of Lemma 2 in §7.3 of Bosch–Lütkebohmert–Raynaud: a connected smooth commutative group over an algebraically closed field is divisible by every integer invertible in the field. It is used in the study of Néron models and Jacobians of good reduction, in particular in the treatment of Riemann forms and level pairings and in the Čerednik–Drinfeld constructions with fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_nsmul_surjective_of_isAlgClosed_of_connectedSpace.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.nsmul_surjective_of_isAlgClosed_of_connectedSpace
    {K : Type u} [Field K] [IsAlgClosed K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}
    [Smooth f] [ConnectedSpace A]
    (G : RelativeGroupLaw K f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (n : ℕ) (hn : IsUnit (n : K)) :
    Function.Surjective (G.nsmul (𝟙 (Spec (CommRingCat.of K))) n) := by sorry
