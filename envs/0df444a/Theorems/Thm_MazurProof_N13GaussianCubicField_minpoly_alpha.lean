-- Prove2me | Theorems.Thm_MazurProof_N13GaussianCubicField_minpoly_alpha
-- name    : MazurProof.N13GaussianCubicField.minpoly_alpha
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T06:17:49.032878+00:00
-- url     : https://prove2.me/theorems/5308c522-bf15-485f-9897-8267336ba251
-- title:
--   Mazur 13 port: minpoly_alpha
-- statement:
--   The integral minimal polynomial is exactly the translated cubic.
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13GaussianCubicField.lean#L121

import Mathlib
import Definitions.Def_MazurN13_L3

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13GaussianCubicField
open Algebra Module Polynomial
open scoped nonZeroDivisors
open N13GaussianGlobalArithmetic
attribute [local instance] MazurProof.N13GaussianCubicField.instFactIrreduciblePolynomialKHK
attribute [local instance] MazurProof.N13GaussianCubicField.fieldL
attribute [local instance] MazurProof.N13GaussianCubicField.finiteKL
attribute [local instance] MazurProof.N13GaussianCubicField.separableKL

theorem MazurProof.N13GaussianCubicField.minpoly_alpha : minpoly GI alpha = h := by sorry
