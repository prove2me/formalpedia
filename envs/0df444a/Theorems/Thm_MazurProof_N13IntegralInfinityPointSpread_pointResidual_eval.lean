-- Prove2me | Theorems.Thm_MazurProof_N13IntegralInfinityPointSpread_pointResidual_eval
-- name    : MazurProof.N13IntegralInfinityPointSpread.pointResidual_eval
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T04:58:18.048985+00:00
-- url     : https://prove2.me/theorems/c3b86712-712c-459c-acc3-7547ae72ba71
-- title:
--   Mazur 13 port: pointResidual_eval
-- statement:
--   Supporting lemma `pointResidual_eval` (namespace `MazurProof.N13IntegralInfinityPointSpread`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13IntegralInfinityPointSpread.lean#L84

import Mathlib
import Definitions.Def_MazurN13_L2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13IntegralInfinityPointSpread
open Polynomial
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13IntegralInfinityPointSpread.instFactPrimeOfNatNat_fLT

theorem MazurProof.N13IntegralInfinityPointSpread.pointResidual_eval (P : IntegralInfinityPoint) : (pointResidual P).eval P.1.1 = 0 := by sorry
