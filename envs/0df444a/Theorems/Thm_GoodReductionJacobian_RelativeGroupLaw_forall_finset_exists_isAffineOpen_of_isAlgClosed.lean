-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_forall_finset_exists_isAffineOpen_of_isAlgClosed
-- name    : GoodReductionJacobian.RelativeGroupLaw.forall_finset_exists_isAffineOpen_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/e9f65cce-afa9-5eb0-9f5a-eb1e41e6cd17
-- title:
--   Finite sets in an abelian scheme lie in one affine open
-- statement:
--   Let $k$ be an algebraically closed field and let $f : A \to \operatorname{Spec} k$ be a morphism of schemes. Assume given a term $L$ of `RelativeGroupLaw k f`, that is, for every $k$-scheme $t : T \to \operatorname{Spec} k$ a group structure on the set $\{\varphi : T \to A \mid \varphi$ followed by $f$ equals $t\}$ of $T$-points of $A$ over $k$: operations `mul`, `one`, `inv` for each such $t$, satisfying associativity, both unit laws and the left inverse law, and with `mul` natural in $T$ in the sense that for $\psi : T' \to T$ with $\psi$ followed by $t$ equal to $t'$, composition with $\psi$ carries the product of two $T$-points to the product of their pullbacks. Assume in addition the bundle `AbelianSchemePropertyBundle k f`: $f$ is smooth, $f$ is proper, for every point $s$ of $\operatorname{Spec} k$ the fibre $f^{-1}(s)$ is connected (in particular the underlying space of $A$ is non-empty and connected), and the set of relative group laws on $f$ is non-empty. Then for every finite set $S$ of points of the scheme $A$ there is an open subset $U$ of $A$ which is an affine open and contains every element of $S$.
--
--   This is the classical fact that a finite set of points of an abelian variety over an algebraically closed field is contained in a single affine open, proved by translating a fixed affine open by suitable rational points; only smoothness, properness, connectedness and the existence of a group law on the functor of points are used, not projectivity. It supplies the affine-covering hypothesis needed when quotients of an abelian scheme by a finite flat subgroup are constructed affine-locally, and is cited in the construction of the quotient cores of fake elliptic curves in the Čerednik–Drinfel'd setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_forall_finset_exists_isAffineOpen_of_isAlgClosed.lean

import Definitions.Def_JacJ1Iface

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.forall_finset_exists_isAffineOpen_of_isAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)
    (hA : AbelianSchemePropertyBundle k f) :
    ∀ S : Finset A, ∃ U : A.Opens, IsAffineOpen U ∧ ∀ x ∈ S, x ∈ U := by sorry
