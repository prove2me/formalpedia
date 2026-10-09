-- Prove2me | Theorems.Thm_MazurProof_SexticMumford_IntegralOrientedRep_primitivePartUnit_mul_contentUnit
-- name    : MazurProof.SexticMumford.IntegralOrientedRep.primitivePartUnit_mul_contentUnit
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T06:49:43.801135+00:00
-- url     : https://prove2.me/theorems/1a21d861-205e-4a3e-a322-e63b00dd78ac
-- title:
--   Mazur 13 port: primitivePartUnit_mul_contentUnit
-- statement:
--   Supporting lemma `primitivePartUnit_mul_contentUnit` (namespace `MazurProof.SexticMumford.IntegralOrientedRep`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/SexticMumfordPrimitivePart.lean#L326

import Mathlib
import Definitions.Def_MazurN13_L3

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.SexticMumford MazurProof.SexticMumford.IntegralOrientedRep
open Polynomial
open scoped nonZeroDivisors
universe u
variable {K : Type u} [Field K]
variable (M : Model K)
variable (O : InfinityOrder M)

theorem MazurProof.SexticMumford.IntegralOrientedRep.primitivePartUnit_mul_contentUnit (R : IntegralOrientedRep M) : R.primitivePartUnit M * toPrincipalIdeal (CoordinateRing M) (FunctionField M) (R.contentUnit M) = R.unit := by sorry
