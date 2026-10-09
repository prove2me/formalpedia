-- Prove2me | Theorems.Thm_MazurProof_N13MumfordInfinityBalance_f_sub_sqrtInfinity_sq
-- name    : MazurProof.N13MumfordInfinityBalance.f_sub_sqrtInfinity_sq
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T03:30:52.24888+00:00
-- url     : https://prove2.me/theorems/e806a0f8-7a9c-4cba-9baa-4c1b881721f5
-- title:
--   Mazur 13 port: f_sub_sqrtInfinity_sq
-- statement:
--   Supporting lemma `f_sub_sqrtInfinity_sq` (namespace `MazurProof.N13MumfordInfinityBalance`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13MumfordInfinityBalance.lean#L58

import Mathlib
import Definitions.Def_MazurN13_L0

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13MumfordInfinityBalance
open Polynomial
open scoped LaurentSeries nonZeroDivisors
universe u
variable {K : Type u} [Field K] [CharZero K]
open MazurProof
open MazurProof.SexticMumford
omit [CharZero K]

theorem MazurProof.N13MumfordInfinityBalance.f_sub_sqrtInfinity_sq : N13Mumford.f K - (sqrtInfinity : K[X]) ^ 2 = 4 * X * (X + 1) := by sorry
