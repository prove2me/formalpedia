-- Prove2me | Theorems.Thm_MazurProof_N13FormalInfinityChart_infinityCurve_relation
-- name    : MazurProof.N13FormalInfinityChart.infinityCurve_relation
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T04:30:41.524496+00:00
-- url     : https://prove2.me/theorems/3aa4f7a7-a132-4684-84e8-e11940ba41f1
-- title:
--   Mazur 13 port: infinityCurve_relation
-- statement:
--   The overlap coordinate `v` satisfies the complete-chart equation.
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13FormalInfinityChart.lean#L114

import Mathlib
import Definitions.Def_MazurN13_L2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13FormalInfinityChart
open Polynomial
open HahnSeries
open scoped PowerSeries LaurentSeries
attribute [local instance] MazurProof.N13FormalInfinityChart.instFactPrimeOfNatNat_fLT

theorem MazurProof.N13FormalInfinityChart.infinityCurve_relation : infinityCurvePoly.eval₂ infinityCoeffMap N13FormalCurveOverlap.vClass = 0 := by sorry
