-- Prove2me | Theorems.Thm_MazurProof_N13Infinity_coordinateToAlgebraic_injective
-- name    : MazurProof.N13Infinity.coordinateToAlgebraic_injective
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T03:50:44.916177+00:00
-- url     : https://prove2.me/theorems/6ec54ea5-1dbf-432f-a0b4-8d17a88560a2
-- title:
--   Mazur 13 port: coordinateToAlgebraic_injective
-- statement:
--   Supporting lemma `coordinateToAlgebraic_injective` (namespace `MazurProof.N13Infinity`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13Infinity.lean#L124

import Mathlib
import Definitions.Def_MazurN13_L1

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13Infinity
open Polynomial
open scoped LaurentSeries PowerSeries
universe u
variable (K : Type u) [Field K] [CharZero K]

theorem MazurProof.N13Infinity.coordinateToAlgebraic_injective : Function.Injective (coordinateToAlgebraic K) := by sorry
