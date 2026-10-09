-- Prove2me | Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_mumfordIdeal_mul_conj_integral
-- name    : MazurProof.N13GoodCoordinateRingTwo.mumfordIdeal_mul_conj_integral
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T03:28:02.711293+00:00
-- url     : https://prove2.me/theorems/33be6283-605d-42bc-88ac-71e6e8f2fcb0
-- title:
--   Mazur 13 port: mumfordIdeal_mul_conj_integral
-- statement:
--   The characteristic-two generalized graph ideal satisfies `(u,Y-v)(u,Y+h+v)=(u)`.
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13GoodCoordinateRingTwo.lean#L572

import Mathlib
import Definitions.Def_MazurN13_L0

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13GoodCoordinateRingTwo
open Polynomial
open FractionalIdeal (coeIdeal_mul)
open scoped nonZeroDivisors

theorem MazurProof.N13GoodCoordinateRingTwo.mumfordIdeal_mul_conj_integral (D : SemiMumford) : mumfordIdeal D.u D.v * mumfordIdeal D.u (conjugateV D.v) = Ideal.span ({xClass D.u} : Set CoordinateRing) := by sorry
