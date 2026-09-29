-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isAffineOpen_forall_mem_of_smooth_of_henselianLocalRing
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_isAffineOpen_forall_mem_of_smooth_of_henselianLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/282e7cf3-b894-5e89-86fc-5395d79abaff
-- title:
--   Finite sets of points of a smooth separated group scheme over a henselian DVR lie in an affine open
-- statement:
--   Let $R$ be a commutative ring which is a domain and a discrete valuation ring, and which is in addition a henselian local ring. Let $B$ be a scheme and $g\colon B \to \operatorname{Spec} R$ a morphism that is smooth, separated and quasi-compact. Suppose given a term $LB$ of `RelativeGroupLaw R g`, that is: for every scheme $T$ and every morphism $t\colon T \to \operatorname{Spec} R$, a multiplication, a distinguished element and an inversion on the set $\{\varphi : T \to B \mid \varphi \text{ followed by } g = t\}$ of $T$-points of $B$ over $t$, such that multiplication is associative, the distinguished element is a two-sided unit, inversion is a left inverse, and multiplication commutes with precomposition by any $\psi\colon T' \to T$ with $\psi$ followed by $t$ equal to $t'$ (naturality is imposed only on the multiplication, not on the unit or the inversion). Let $S$ be a finite set of points of the underlying topological space of $B$. Then there exists an open subset $U$ of $B$ which is an affine open and which contains every $b \in S$.
--
--   This is the henselian case of the affine-neighbourhood property (property AF, also attributed to Chevalley and Kleiman) for smooth separated group schemes of finite type over a discrete valuation ring: any finite set of points, including points in distinct fibres, is contained in a single affine open. It is used in the construction of relative group laws on open subschemes in the étale-descent step for Néron models over a henselian base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isAffineOpen_forall_mem_of_smooth_of_henselianLocalRing.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_isAffineOpen_forall_mem_of_smooth_of_henselianLocalRing
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} [Smooth g] [IsSeparated g] [QuasiCompact g]
    (LB : RelativeGroupLaw R g) (S : Finset B) :
    ∃ U : B.Opens, IsAffineOpen U ∧ ∀ b ∈ S, b ∈ U := by sorry
