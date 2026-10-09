-- Prove2me | Theorems.Thm_MazurProof_N13BranchLeading_branch_min_order
-- name    : MazurProof.N13BranchLeading.branch_min_order
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T04:13:52.181132+00:00
-- url     : https://prove2.me/theorems/a47fd585-6dec-4b4c-a940-bb93a0ecfa6a
-- title:
--   Mazur 13 port: branch_min_order
-- statement:
--   Supporting lemma `branch_min_order` (namespace `MazurProof.N13BranchLeading`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13BranchLeading.lean#L100

import Mathlib
import Definitions.Def_MazurN13_L2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13BranchLeading
open Polynomial
open scoped LaurentSeries
universe u
variable (K : Type u) [Field K] [CharZero K]

theorem MazurProof.N13BranchLeading.branch_min_order (p q : K[X]) (hz : N13BranchNorm.linearFunction K p q ≠ 0) : min (N13Infinity.coordinateToLaurent K (N13BranchNorm.linearFunction K p q)).order (N13InfinityMinus.coordinateToLaurentMinus K (N13BranchNorm.linearFunction K p q)).order = -(poleDegree K p q : ℤ) := by sorry
