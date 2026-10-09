-- Prove2me | Theorems.Thm_MazurProof_N13TwoAdicAbelChartRecover_NearBaseMumford_u_eval_negOne_mem
-- name    : MazurProof.N13TwoAdicAbelChartRecover.NearBaseMumford.u_eval_negOne_mem
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T03:47:51.265593+00:00
-- url     : https://prove2.me/theorems/d523b6c4-5e40-418f-8d08-29ea4a5400ba
-- title:
--   Mazur 13 port: u_eval_negOne_mem
-- statement:
--   Supporting lemma `u_eval_negOne_mem` (namespace `MazurProof.N13TwoAdicAbelChartRecover.NearBaseMumford`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13TwoAdicAbelChartRecover.lean#L134

import Mathlib
import Definitions.Def_MazurN13_L1

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13TwoAdicAbelChartRecover MazurProof.N13TwoAdicAbelChartRecover.NearBaseMumford
open Polynomial
open scoped nonZeroDivisors
variable (D : NearBaseMumford)
attribute [local instance] MazurProof.N13TwoAdicAbelChartRecover.instFactPrimeOfNatNat_fLT

theorem MazurProof.N13TwoAdicAbelChartRecover.NearBaseMumford.u_eval_negOne_mem : D.u.eval (-1) ∈ maximal := by sorry
