-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isAffineOpen_forall_mem_of_isAffineOpen_of_forall_specializes_of_henselianLocalRing
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_isAffineOpen_forall_mem_of_isAffineOpen_of_forall_specializes_of_henselianLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/afc6d7f1-6e5e-5c36-a443-243ca4975a0a
-- title:
--   Finite sets lie in affine opens, over a henselian DVR
-- statement:
--   Let $R$ be a discrete valuation ring (a domain, with its local ring henselian), let $B$ be a scheme and let $g\colon B \to \operatorname{Spec} R$ be smooth, separated and quasi-compact. Suppose $g$ carries a relative group law $L_B$, that is: for every scheme $T$ and every morphism $t\colon T \to \operatorname{Spec} R$ a multiplication, unit and inversion on the set of $R$-morphisms $T \to B$ lifting $t$ (pairs $\varphi$ with $\varphi \ggg g = t$), satisfying associativity, both unit laws and left inverses, and with multiplication compatible with precomposition by any $\psi\colon T' \to T$ over $\operatorname{Spec} R$. Let $U$ be an open subscheme of $B$ which is affine ($hU_1$) and which contains every point $b$ of $B$ that is maximal in its fibre, in the sense that the only $y \in B$ with $b \in \overline{\{y\}}$ and $g(y) = g(b)$ is $y = b$ ($hU_2$); thus $U$ contains all generic points of the fibres of $g$. Then for every finite set $S$ of points of $B$ there is an affine open subscheme $V$ of $B$ containing every $b \in S$.
--
--   This is the translation argument showing that on a smooth separated quasi-compact group scheme over a henselian discrete valuation ring, an affine open meeting every fibre in a dense subset can be translated so as to capture any prescribed finite set of points; it is the step behind the quasi-projectivity/affineness arguments for Néron models. It feeds the variant [`GoodReductionJacobian.RelativeGroupLaw.exists_isAffineOpen_forall_mem_of_smooth_of_henselianLocalRing`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_isAffineOpen_forall_mem_of_smooth_of_henselianLocalRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isAffineOpen_forall_mem_of_isAffineOpen_of_forall_specializes_of_henselianLocalRing.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_isAffineOpen_forall_mem_of_isAffineOpen_of_forall_specializes_of_henselianLocalRing
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} [Smooth g] [IsSeparated g] [QuasiCompact g]
    (LB : RelativeGroupLaw R g) (U : B.Opens) (hU₁ : IsAffineOpen U)
    (hU₂ : ∀ b : B, (∀ y : B, y ⤳ b → g.base y = g.base b → y = b) → b ∈ U)
    (S : Finset B) :
    ∃ V : B.Opens, IsAffineOpen V ∧ ∀ b ∈ S, b ∈ V := by sorry
