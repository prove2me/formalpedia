-- Prove2me | Theorems.Thm_MazurProof_N13GaussianDifferentSupport_relativeGaussianTwoIdeal_isPrime
-- name    : MazurProof.N13GaussianDifferentSupport.relativeGaussianTwoIdeal_isPrime
-- status  : Open
-- author  : @xuanji
-- created : 2026-10-09T03:28:49.197855+00:00
-- url     : https://prove2.me/theorems/01fd449e-681e-4001-81a6-285f04cef5f2
-- title:
--   Mazur 13 port: relativeGaussianTwoIdeal_isPrime
-- statement:
--   Supporting lemma `relativeGaussianTwoIdeal_isPrime` (namespace `MazurProof.N13GaussianDifferentSupport`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13GaussianDifferentSupport.lean#L725

import Mathlib
import Definitions.Def_MazurN13_L0

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13GaussianDifferentSupport
open Algebra Module Polynomial
open scoped nonZeroDivisors
open N13GaussianFieldEquiv
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare

theorem MazurProof.N13GaussianDifferentSupport.relativeGaussianTwoIdeal_isPrime : relativeGaussianTwoIdeal.IsPrime := by sorry
