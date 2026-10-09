-- Prove2me | Theorems.Thm_MazurProof_N13GaussianGlobalReductionTwo_shiftedTheta_root_h
-- name    : MazurProof.N13GaussianGlobalReductionTwo.shiftedTheta_root_h
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T07:50:22.44998+00:00
-- url     : https://prove2.me/theorems/4383e098-4275-4ed7-9486-624f3dfb56e4
-- title:
--   Mazur 13 port: shiftedTheta_root_h
-- statement:
--   Supporting lemma `shiftedTheta_root_h` (namespace `MazurProof.N13GaussianGlobalReductionTwo`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13GaussianGlobalReductionTwo.lean#L86

import Mathlib
import Definitions.Def_MazurN13_L4

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13GaussianGlobalReductionTwo
open Polynomial
open N13GaussianGlobalArithmetic
open N13GaussianCubicField
open N13GaussianNumberField
open N13GaussianOrderTwo
attribute [local instance] MazurProof.N13GaussianGlobalReductionTwo.hKIrreducibleFact
attribute [local instance] MazurProof.N13GaussianGlobalReductionTwo.fieldL
attribute [local instance] MazurProof.N13GaussianGlobalReductionTwo.intAlgebraL
attribute [local instance] MazurProof.N13GaussianGlobalReductionTwo.intAlgebraGI
attribute [local instance] MazurProof.N13GaussianGlobalReductionTwo.intAlgebraRelativeO
attribute [local instance] MazurProof.N13GaussianGlobalReductionTwo.intAlgebraAbsoluteO
attribute [local instance] MazurProof.N13GaussianGlobalReductionTwo.giAlgebraOrder

theorem MazurProof.N13GaussianGlobalReductionTwo.shiftedTheta_root_h : aeval (N13GaussianOrderTwo.theta - 9 : Order) N13GaussianGlobalArithmetic.h = 0 := by sorry
