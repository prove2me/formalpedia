-- Prove2me | Theorems.Thm_MazurProof_N13IntegralCurveProperties_infinity_tClass_mem_nonZeroDivisors
-- name    : MazurProof.N13IntegralCurveProperties.infinity_tClass_mem_nonZeroDivisors
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T04:50:54.231986+00:00
-- url     : https://prove2.me/theorems/6dae126f-bdcb-4176-990a-5e62852d9ea0
-- title:
--   Mazur 13 port: infinity_tClass_mem_nonZeroDivisors
-- statement:
--   The infinity parameter is a non-zero-divisor. This is the free-module argument: multiplication by `t` is scalar multiplication by the nonzero polynomial `X` on a free `ℤ₂[t]`-module.
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13IntegralCurveProperties.lean#L69

import Mathlib
import Definitions.Def_MazurN13_L2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13IntegralCurveProperties
open CategoryTheory
open Polynomial
open Set Topology
open AlgebraicGeometry
attribute [local instance] MazurProof.N13IntegralCurveProperties.instFactPrimeOfNatNat_fLT

theorem MazurProof.N13IntegralCurveProperties.infinity_tClass_mem_nonZeroDivisors : N13IntegralInfinityChart.tClass ∈ nonZeroDivisors InfinityCurve := by sorry
