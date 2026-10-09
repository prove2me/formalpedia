-- Prove2me | Theorems.Thm_MazurProof_N13TwoAdicAbelChartRecover_NearBaseMumford_derivative_eval_negOne_isUnit
-- name    : MazurProof.N13TwoAdicAbelChartRecover.NearBaseMumford.derivative_eval_negOne_isUnit
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T03:47:41.234228+00:00
-- url     : https://prove2.me/theorems/3f41f39d-55af-465c-b866-afc8bd3a7df0
-- title:
--   Mazur 13 port: derivative_eval_negOne_isUnit
-- statement:
--   Supporting lemma `derivative_eval_negOne_isUnit` (namespace `MazurProof.N13TwoAdicAbelChartRecover.NearBaseMumford`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13TwoAdicAbelChartRecover.lean#L149

import Mathlib
import Definitions.Def_MazurN13_L1

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13TwoAdicAbelChartRecover MazurProof.N13TwoAdicAbelChartRecover.NearBaseMumford
open Polynomial
open scoped nonZeroDivisors
variable (D : NearBaseMumford)
attribute [local instance] MazurProof.N13TwoAdicAbelChartRecover.instFactPrimeOfNatNat_fLT

theorem MazurProof.N13TwoAdicAbelChartRecover.NearBaseMumford.derivative_eval_negOne_isUnit : IsUnit (D.u.derivative.eval (-1)) := by sorry
