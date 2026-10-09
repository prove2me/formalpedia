-- Prove2me | Theorems.Thm_MazurProof_N13InfinityLineSpecialRestriction_map_pointIdeal
-- name    : MazurProof.N13InfinityLineSpecialRestriction.map_pointIdeal
-- status  : Open
-- author  : @xuanji
-- created : 2026-10-09T08:02:07.172217+00:00
-- url     : https://prove2.me/theorems/f2ebf30d-1477-4b32-a6d4-83f56c757a6d
-- title:
--   Mazur 13 port: map_pointIdeal
-- statement:
--   The special point ideal obtained by reducing an integral infinity point has exactly the reduced coordinates of that point.
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13InfinityLineSpecialRestriction.lean#L54

import Mathlib
import Definitions.Def_MazurN13_L4

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13InfinityLineSpecialRestriction
open Polynomial
attribute [local instance] MazurProof.N13InfinityLineSpecialRestriction.instFactPrimeOfNatNat_fLT

theorem MazurProof.N13InfinityLineSpecialRestriction.map_pointIdeal (P : IntegralInfinityPoint) : Ideal.map N13IntegralInfinityReduction.reduceCoordinate (N13IntegralInfinityPointSpread.pointIdeal P) = N13SpecialDivisorCharts.infinityPointIdeal (N13IntegralInfinityReduction.reduceBase P.1.1) (N13IntegralInfinityReduction.reduceBase P.1.2) := by sorry
