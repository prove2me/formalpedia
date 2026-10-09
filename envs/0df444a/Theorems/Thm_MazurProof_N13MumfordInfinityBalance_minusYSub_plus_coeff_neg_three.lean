-- Prove2me | Theorems.Thm_MazurProof_N13MumfordInfinityBalance_minusYSub_plus_coeff_neg_three
-- name    : MazurProof.N13MumfordInfinityBalance.minusYSub_plus_coeff_neg_three
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T05:06:39.713548+00:00
-- url     : https://prove2.me/theorems/57f855e9-7be8-4eae-9849-1a40012e61b3
-- title:
--   Mazur 13 port: minusYSub_plus_coeff_neg_three
-- statement:
--   Supporting lemma `minusYSub_plus_coeff_neg_three` (namespace `MazurProof.N13MumfordInfinityBalance`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13MumfordInfinityBalance.lean#L475

import Mathlib
import Definitions.Def_MazurN13_L2

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

theorem MazurProof.N13MumfordInfinityBalance.minusYSub_plus_coeff_neg_three (hdeg : D.u.natDegree ≤ 2) : (N13Infinity.coordinateToLaurent K (ySubClass (N13Mumford.model K) (minusLift D))).coeff (-3 : ℤ) = 2 := by sorry
