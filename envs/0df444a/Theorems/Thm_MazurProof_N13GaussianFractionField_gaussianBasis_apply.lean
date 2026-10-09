-- Prove2me | Theorems.Thm_MazurProof_N13GaussianFractionField_gaussianBasis_apply
-- name    : MazurProof.N13GaussianFractionField.gaussianBasis_apply
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T04:30:50.868668+00:00
-- url     : https://prove2.me/theorems/6a6091b8-003d-455d-8926-1b6bb14777b0
-- title:
--   Mazur 13 port: gaussianBasis_apply
-- statement:
--   Supporting lemma `gaussianBasis_apply` (namespace `MazurProof.N13GaussianFractionField`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13GaussianFractionField.lean#L176

import Mathlib
import Definitions.Def_MazurN13_L2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13GaussianFractionField
open Module
open Polynomial
open scoped nonZeroDivisors
open scoped Matrix
open N13GaussianGlobalArithmetic

theorem MazurProof.N13GaussianFractionField.gaussianBasis_apply (j : Fin 2) : gaussianBasis j = algebraMap GI K (gaussianIntBasis j) := by sorry
