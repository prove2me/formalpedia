-- Prove2me | Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_no_artinSchreier_polynomial_root
-- name    : MazurProof.N13GoodCoordinateRingTwo.no_artinSchreier_polynomial_root
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T03:27:45.729757+00:00
-- url     : https://prove2.me/theorems/dedfbaed-48c2-4499-9a74-f44cc69a19a9
-- title:
--   Mazur 13 port: no_artinSchreier_polynomial_root
-- statement:
--   Supporting lemma `no_artinSchreier_polynomial_root` (namespace `MazurProof.N13GoodCoordinateRingTwo`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13GoodCoordinateRingTwo.lean#L128

import Mathlib
import Definitions.Def_MazurN13_L0

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13GoodCoordinateRingTwo
open Polynomial
open FractionalIdeal (coeIdeal_mul)
open scoped nonZeroDivisors

theorem MazurProof.N13GoodCoordinateRingTwo.no_artinSchreier_polynomial_root (q : K[X]) : q ^ 2 + hPoly * q ≠ rhsPoly := by sorry
