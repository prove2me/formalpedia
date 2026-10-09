-- Prove2me | Theorems.Thm_MazurProof_N13ReciprocalInfinityContraction_xbar_mul_tbar
-- name    : MazurProof.N13ReciprocalInfinityContraction.xbar_mul_tbar
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T08:18:37.773826+00:00
-- url     : https://prove2.me/theorems/f1417d7a-569c-47a3-83d3-8987294edf7f
-- title:
--   Mazur 13 port: xbar_mul_tbar
-- statement:
--   Supporting lemma `xbar_mul_tbar` (namespace `MazurProof.N13ReciprocalInfinityContraction`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13ReciprocalInfinityContraction.lean#L135

import Mathlib
import Definitions.Def_MazurN13_L4

open MazurProof MazurProof.N13ReciprocalInfinityContraction
open Polynomial
open Module
open scoped nonZeroDivisors TensorProduct
attribute [local instance] MazurProof.N13ReciprocalInfinityContraction.instFactPrimeOfNatNat_fLT
attribute [local instance] MazurProof.N13ReciprocalInfinityContraction.baseSpecialAlgebra

theorem MazurProof.N13ReciprocalInfinityContraction.xbar_mul_tbar (D : SexticMumford.Mumford Model) (hdeg : D.u.natDegree = 2) (h0 : D.u.coeff 0 ≠ 0) : xbar D * tbar D = 1 := by sorry
