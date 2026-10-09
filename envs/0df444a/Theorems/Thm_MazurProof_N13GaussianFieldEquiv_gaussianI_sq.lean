-- Prove2me | Theorems.Thm_MazurProof_N13GaussianFieldEquiv_gaussianI_sq
-- name    : MazurProof.N13GaussianFieldEquiv.gaussianI_sq
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T06:22:52.622239+00:00
-- url     : https://prove2.me/theorems/db893cff-01af-4dc7-bfed-3102fa7a64b4
-- title:
--   Mazur 13 port: gaussianI_sq
-- statement:
--   Supporting lemma `gaussianI_sq` (namespace `MazurProof.N13GaussianFieldEquiv`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13GaussianFieldEquiv.lean#L60

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

theorem MazurProof.N13GaussianFieldEquiv.gaussianI_sq : gaussianI ^ 2 = -1 := by sorry
