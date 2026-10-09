-- Prove2me | Theorems.Thm_MazurProof_N13IntegralInfinityGraphJacobian_graphIdeal_isUnit
-- name    : MazurProof.N13IntegralInfinityGraphJacobian.graphIdeal_isUnit
-- status  : Open
-- author  : @xuanji
-- created : 2026-10-09T04:52:52.357927+00:00
-- url     : https://prove2.me/theorems/b2976cf4-9bbc-4401-b093-62b686680370
-- title:
--   Mazur 13 port: graphIdeal_isUnit
-- statement:
--   Every nondegenerate integral polynomial graph on the ordinary infinity chart is invertible.
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13IntegralInfinityGraphJacobian.lean#L243

import Mathlib
import Definitions.Def_MazurN13_L2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13IntegralInfinityGraphJacobian
open Polynomial
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13IntegralInfinityGraphJacobian.instFactPrimeOfNatNat_fLT

theorem MazurProof.N13IntegralInfinityGraphJacobian.graphIdeal_isUnit (D : GraphData) (hu : D.u ≠ 0) : IsUnit ((GeneralizedGraphIdealCore.graphIdeal xClassHom yClass D.u D.v : Ideal InfinityCurve) : InfinityFractionalIdeal) := by sorry
