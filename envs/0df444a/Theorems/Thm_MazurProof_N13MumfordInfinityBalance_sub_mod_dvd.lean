-- Prove2me | Theorems.Thm_MazurProof_N13MumfordInfinityBalance_sub_mod_dvd
-- name    : MazurProof.N13MumfordInfinityBalance.sub_mod_dvd
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T03:25:14.172173+00:00
-- url     : https://prove2.me/theorems/24da684d-bb13-46c4-9bd4-67e0afbd69e0
-- title:
--   Mazur 13 port: sub_mod_dvd
-- statement:
--   Supporting lemma `sub_mod_dvd` (namespace `MazurProof.N13MumfordInfinityBalance`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13MumfordInfinityBalance.lean#L89

import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial
open scoped LaurentSeries nonZeroDivisors
universe u
variable {K : Type u} [Field K] [CharZero K]
omit [CharZero K]

theorem MazurProof.N13MumfordInfinityBalance.sub_mod_dvd (p u : K[X]) : u ∣ p - p % u := by sorry
