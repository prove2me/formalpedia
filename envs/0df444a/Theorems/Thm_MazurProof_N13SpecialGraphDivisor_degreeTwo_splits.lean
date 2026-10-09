-- Prove2me | Theorems.Thm_MazurProof_N13SpecialGraphDivisor_degreeTwo_splits
-- name    : MazurProof.N13SpecialGraphDivisor.degreeTwo_splits
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T03:33:34.999187+00:00
-- url     : https://prove2.me/theorems/feb7d11b-b94d-4791-ac77-c044d4a50fb1
-- title:
--   Mazur 13 port: degreeTwo_splits
-- statement:
--   Supporting lemma `degreeTwo_splits` (namespace `MazurProof.N13SpecialGraphDivisor`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13SpecialGraphDivisor.lean#L34

import Mathlib
import Definitions.Def_MazurN13_L0

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13SpecialGraphDivisor
open Polynomial
open scoped Sym2
open MazurProof.N13GoodCoordinateRingTwo
attribute [local instance] MazurProof.N13SpecialGraphDivisor.instFactPrimeOfNatNat_fLT

theorem MazurProof.N13SpecialGraphDivisor.degreeTwo_splits (D : SemiMumford) (hdeg : D.u.natDegree = 2) : D.u.Splits := by sorry
