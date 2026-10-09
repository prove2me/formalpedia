-- Prove2me | Theorems.Thm_MazurProof_N13MumfordInfinityBalance_balanceInfinity_class
-- name    : MazurProof.N13MumfordInfinityBalance.balanceInfinity_class
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T06:44:51.670974+00:00
-- url     : https://prove2.me/theorems/cad75ceb-d020-4139-94e7-0c583e9abf22
-- title:
--   Mazur 13 port: balanceInfinity_class
-- statement:
--   Supporting lemma `balanceInfinity_class` (namespace `MazurProof.N13MumfordInfinityBalance`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13MumfordInfinityBalance.lean#L874

import Mathlib
import Definitions.Def_MazurN13_L3

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13MumfordInfinityBalance
open Polynomial
open scoped LaurentSeries nonZeroDivisors
universe u
variable {K : Type u} [Field K] [CharZero K]
open MazurProof
open MazurProof.SexticMumford
variable (D : N13Mumford.SemiMumford K)

theorem MazurProof.N13MumfordInfinityBalance.balanceInfinity_class (E : LowDegree (K := K)) : semiMumfordClass (N13Mumford.model K) (N13Infinity.positiveInfinityOrder K) (balanceInfinity E).toSemi = semiMumfordClass (N13Mumford.model K) (N13Infinity.positiveInfinityOrder K) E.toSemi := by sorry
