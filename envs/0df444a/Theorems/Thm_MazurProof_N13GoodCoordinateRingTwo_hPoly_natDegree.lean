-- Prove2me | Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_hPoly_natDegree
-- name    : MazurProof.N13GoodCoordinateRingTwo.hPoly_natDegree
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T03:28:54.280903+00:00
-- url     : https://prove2.me/theorems/b6e751b4-7236-42c9-8af1-297b5abae99a
-- title:
--   Mazur 13 port: hPoly_natDegree
-- statement:
--   Supporting lemma `hPoly_natDegree` (namespace `MazurProof.N13GoodCoordinateRingTwo`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13GoodCoordinateRingTwo.lean#L48

import Mathlib
import Definitions.Def_MazurN13_L0

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13GoodCoordinateRingTwo
open Polynomial
open FractionalIdeal (coeIdeal_mul)
open scoped nonZeroDivisors

theorem MazurProof.N13GoodCoordinateRingTwo.hPoly_natDegree : hPoly.natDegree = 3 := by sorry
