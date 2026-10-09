-- Prove2me | Theorems.Thm_MazurProof_SexticMumford_mumfordIdeal_mul_conj_integral
-- name    : MazurProof.SexticMumford.mumfordIdeal_mul_conj_integral
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T03:32:44.614764+00:00
-- url     : https://prove2.me/theorems/39c43910-3c78-4d4e-94f5-01c7e0d0a952
-- title:
--   Mazur 13 port: mumfordIdeal_mul_conj_integral
-- statement:
--   Supporting lemma `mumfordIdeal_mul_conj_integral` (namespace `MazurProof.SexticMumford`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/SexticMumfordUnit.lean#L75

import Mathlib
import Definitions.Def_MazurN13_L0

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.SexticMumford
open Polynomial
open FractionalIdeal (coeIdeal_mul)
open scoped nonZeroDivisors
universe u
variable {K : Type u} [Field K]
variable (M : Model K)

theorem MazurProof.SexticMumford.mumfordIdeal_mul_conj_integral (D : SemiMumford M) : mumfordIdeal M D.u D.v * mumfordIdeal M D.u (-D.v) = Ideal.span ({xClass M D.u} : Set (CoordinateRing M)) := by sorry
