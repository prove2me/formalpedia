-- Prove2me | Theorems.Thm_MazurProof_N13TwoAdicAbelChartRecover_NearBaseMumford_diskPair_u_dvd_v_sub
-- name    : MazurProof.N13TwoAdicAbelChartRecover.NearBaseMumford.diskPair_u_dvd_v_sub
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T05:40:40.748536+00:00
-- url     : https://prove2.me/theorems/ad4db939-0918-426a-937e-781e9e02d23c
-- title:
--   Mazur 13 port: diskPair_u_dvd_v_sub
-- statement:
--   The original graph polynomial and the recovered interpolant agree modulo the recovered quadratic.
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13TwoAdicAbelChartRecover.lean#L293

import Mathlib
import Definitions.Def_MazurN13_L2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13TwoAdicAbelChartRecover MazurProof.N13TwoAdicAbelChartRecover.NearBaseMumford
open Polynomial
open scoped nonZeroDivisors
variable (D : NearBaseMumford)
attribute [local instance] MazurProof.N13TwoAdicAbelChartRecover.instFactPrimeOfNatNat_fLT

theorem MazurProof.N13TwoAdicAbelChartRecover.NearBaseMumford.diskPair_u_dvd_v_sub : D.diskPair.u ∣ D.v - D.diskPair.v := by sorry
