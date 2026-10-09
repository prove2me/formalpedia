-- Prove2me | Theorems.Thm_MazurProof_N13BranchNorm_evalPoly_ne_zero
-- name    : MazurProof.N13BranchNorm.evalPoly_ne_zero
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T03:27:50.789059+00:00
-- url     : https://prove2.me/theorems/d5007059-179f-4777-91f0-c3462528df14
-- title:
--   Mazur 13 port: evalPoly_ne_zero
-- statement:
--   Supporting lemma `evalPoly_ne_zero` (namespace `MazurProof.N13BranchNorm`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13BranchNorm.lean#L49

import Mathlib
import Definitions.Def_MazurN13_L0

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13BranchNorm
open Polynomial
open scoped LaurentSeries
universe u
variable (K : Type u) [Field K] [CharZero K]
omit [CharZero K]

theorem MazurProof.N13BranchNorm.evalPoly_ne_zero {p : K[X]} (hp : p ≠ 0) : evalPoly K p ≠ 0 := by sorry
