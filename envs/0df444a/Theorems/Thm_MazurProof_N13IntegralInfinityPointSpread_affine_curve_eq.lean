-- Prove2me | Theorems.Thm_MazurProof_N13IntegralInfinityPointSpread_affine_curve_eq
-- name    : MazurProof.N13IntegralInfinityPointSpread.affine_curve_eq
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T04:55:35.315242+00:00
-- url     : https://prove2.me/theorems/760b3761-8791-4a94-b009-23235e7f43c7
-- title:
--   Mazur 13 port: affine_curve_eq
-- statement:
--   Weighted homogenization of the infinity point equation gives the exact affine graph factorization.
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13IntegralInfinityPointSpread.lean#L305

import Mathlib
import Definitions.Def_MazurN13_L2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13IntegralInfinityPointSpread
open Polynomial
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13IntegralInfinityPointSpread.instFactPrimeOfNatNat_fLT

theorem MazurProof.N13IntegralInfinityPointSpread.affine_curve_eq (P : IntegralInfinityPoint) : affineV P ^ 2 + N13GeneralizedMumfordIntegral.hPoly (R := R₂) * affineV P - N13GeneralizedMumfordIntegral.rhsPoly (R := R₂) = affineU P * affineW P := by sorry
