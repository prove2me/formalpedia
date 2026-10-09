-- Prove2me | Theorems.Thm_MazurProof_N13Infinity_reverseTail_constantCoeff
-- name    : MazurProof.N13Infinity.reverseTail_constantCoeff
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T03:30:49.27863+00:00
-- url     : https://prove2.me/theorems/3e6e8006-3268-4436-b981-c04adb4a5268
-- title:
--   Mazur 13 port: reverseTail_constantCoeff
-- statement:
--   Supporting lemma `reverseTail_constantCoeff` (namespace `MazurProof.N13Infinity`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13Infinity.lean#L44

import Mathlib
import Definitions.Def_MazurN13_L0

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13Infinity
open Polynomial
open scoped LaurentSeries PowerSeries
universe u
variable (K : Type u) [Field K] [CharZero K]
omit [CharZero K]

theorem MazurProof.N13Infinity.reverseTail_constantCoeff : PowerSeries.constantCoeff (reverseTail K) = 0 := by sorry
