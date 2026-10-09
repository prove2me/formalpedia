-- Prove2me | Theorems.Thm_MazurProof_N13GaussianOrderTwo_i_sq
-- name    : MazurProof.N13GaussianOrderTwo.i_sq
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T04:37:14.605727+00:00
-- url     : https://prove2.me/theorems/c6740984-f548-4fd2-8cc1-0312887e9719
-- title:
--   Mazur 13 port: i_sq
-- statement:
--   Supporting lemma `i_sq` (namespace `MazurProof.N13GaussianOrderTwo`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13GaussianOrderTwo.lean#L103

import Mathlib
import Definitions.Def_MazurN13_L2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13GaussianOrderTwo
open Polynomial
open scoped CharTwo
open N13LocalDlogTwo
open N13LocalDlogRegimes
open TrivSqZeroExt
open Module

theorem MazurProof.N13GaussianOrderTwo.i_sq : i ^ 2 = -1 := by sorry
