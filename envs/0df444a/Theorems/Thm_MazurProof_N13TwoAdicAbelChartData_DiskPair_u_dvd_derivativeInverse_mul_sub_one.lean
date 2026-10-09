-- Prove2me | Theorems.Thm_MazurProof_N13TwoAdicAbelChartData_DiskPair_u_dvd_derivativeInverse_mul_sub_one
-- name    : MazurProof.N13TwoAdicAbelChartData.DiskPair.u_dvd_derivativeInverse_mul_sub_one
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T03:46:33.235253+00:00
-- url     : https://prove2.me/theorems/751f03d2-5ea1-478c-b180-197a7c3bc92a
-- title:
--   Mazur 13 port: u_dvd_derivativeInverse_mul_sub_one
-- statement:
--   Supporting lemma `u_dvd_derivativeInverse_mul_sub_one` (namespace `MazurProof.N13TwoAdicAbelChartData.DiskPair`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13TwoAdicAbelChartData.lean#L312

import Mathlib
import Definitions.Def_MazurN13_L1

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13TwoAdicAbelChartData MazurProof.N13TwoAdicAbelChartData.DiskPair
open Polynomial
variable (P : DiskPair)
attribute [local instance] MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT

theorem MazurProof.N13TwoAdicAbelChartData.DiskPair.u_dvd_derivativeInverse_mul_sub_one : P.u ∣ P.derivativeInverse * P.verticalDerivative - 1 := by sorry
