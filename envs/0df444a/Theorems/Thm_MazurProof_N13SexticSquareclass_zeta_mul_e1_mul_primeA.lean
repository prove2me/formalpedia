-- Prove2me | Theorems.Thm_MazurProof_N13SexticSquareclass_zeta_mul_e1_mul_primeA
-- name    : MazurProof.N13SexticSquareclass.zeta_mul_e1_mul_primeA
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T05:19:06.158461+00:00
-- url     : https://prove2.me/theorems/6b79475c-a21a-4daf-8eb6-6d99dcaab311
-- title:
--   Mazur 13 port: zeta_mul_e1_mul_primeA
-- statement:
--   Supporting lemma `zeta_mul_e1_mul_primeA` (namespace `MazurProof.N13SexticSquareclass`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13SexticSquareclass.lean#L191

import Mathlib
import Definitions.Def_MazurN13_L2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13SexticSquareclass
open Polynomial

theorem MazurProof.N13SexticSquareclass.zeta_mul_e1_mul_primeA : zeta * e1 * primeA = halfOfPoly B := by sorry
