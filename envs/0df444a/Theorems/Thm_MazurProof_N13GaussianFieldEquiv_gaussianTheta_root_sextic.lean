-- Prove2me | Theorems.Thm_MazurProof_N13GaussianFieldEquiv_gaussianTheta_root_sextic
-- name    : MazurProof.N13GaussianFieldEquiv.gaussianTheta_root_sextic
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T06:31:22.268113+00:00
-- url     : https://prove2.me/theorems/ec089bb4-fb81-40a9-a515-8e9d83784588
-- title:
--   Mazur 13 port: gaussianTheta_root_sextic
-- statement:
--   Supporting lemma `gaussianTheta_root_sextic` (namespace `MazurProof.N13GaussianFieldEquiv`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13GaussianFieldEquiv.lean#L95

import Mathlib
import Definitions.Def_MazurN13_L3

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13GaussianFieldEquiv
open Algebra Module Polynomial
open N13GaussianGlobalArithmetic
attribute [local instance] MazurProof.N13GaussianFieldEquiv.fieldLg
attribute [local instance] MazurProof.N13GaussianFieldEquiv.fieldLs
attribute [local instance] MazurProof.N13GaussianFieldEquiv.finiteKL
attribute [local instance] MazurProof.N13GaussianFieldEquiv.finiteQL

theorem MazurProof.N13GaussianFieldEquiv.gaussianTheta_root_sextic : eval₂ (algebraMap ℚ Lg) gaussianTheta N13SexticSquareclass.f = 0 := by sorry
