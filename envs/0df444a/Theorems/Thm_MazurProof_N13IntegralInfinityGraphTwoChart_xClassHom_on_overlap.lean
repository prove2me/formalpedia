-- Prove2me | Theorems.Thm_MazurProof_N13IntegralInfinityGraphTwoChart_xClassHom_on_overlap
-- name    : MazurProof.N13IntegralInfinityGraphTwoChart.xClassHom_on_overlap
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T04:54:03.925971+00:00
-- url     : https://prove2.me/theorems/79ada37f-77e0-497f-ae3f-c2ffbc22986c
-- title:
--   Mazur 13 port: xClassHom_on_overlap
-- statement:
--   The infinity horizontal coordinate map evaluates polynomials at the Laurent-overlap coordinate `t`.
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13IntegralInfinityGraphTwoChart.lean#L282

import Mathlib
import Definitions.Def_MazurN13_L2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13IntegralInfinityGraphTwoChart
open Polynomial
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13IntegralInfinityGraphTwoChart.instFactPrimeOfNatNat_fLT

theorem MazurProof.N13IntegralInfinityGraphTwoChart.xClassHom_on_overlap (p : Base) : (algebraMap InfinityCurve N13OrdinaryCurveOverlap.InfinityOverlap) (N13IntegralInfinityGraphJacobian.xClassHom p) = p.eval₂ N13OrdinaryCurveOverlap.coefficientToInfinityOverlap N13OrdinaryCurveOverlap.tOverlap := by sorry
