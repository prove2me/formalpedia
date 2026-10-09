-- Prove2me | Theorems.Thm_MazurProof_N13FullNormPairGaussian_norm_gaussianI
-- name    : MazurProof.N13FullNormPairGaussian.norm_gaussianI
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T06:09:00.025623+00:00
-- url     : https://prove2.me/theorems/2a924208-c0ec-4b99-9b68-ea8503eb4115
-- title:
--   Mazur 13 port: norm_gaussianI
-- statement:
--   The absolute norm of `i` is one: the relative norm through the cubic Gaussian extension is `i³ = -i`, whose Gaussian norm is one.
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13FullNormPairGaussian.lean#L65

import Mathlib
import Definitions.Def_MazurN13_L3

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13FullNormPairGaussian
open N13GaussianGlobalArithmetic
attribute [local instance] MazurProof.N13FullNormPairGaussian.fieldLs
attribute [local instance] MazurProof.N13FullNormPairGaussian.fieldLg

theorem MazurProof.N13FullNormPairGaussian.norm_gaussianI : Algebra.norm ℚ N13GaussianFieldEquiv.gaussianI = 1 := by sorry
