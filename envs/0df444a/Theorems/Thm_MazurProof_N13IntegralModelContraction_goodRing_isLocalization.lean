-- Prove2me | Theorems.Thm_MazurProof_N13IntegralModelContraction_goodRing_isLocalization
-- name    : MazurProof.N13IntegralModelContraction.goodRing_isLocalization
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T03:49:15.048867+00:00
-- url     : https://prove2.me/theorems/29803b27-3050-4e6c-bbdb-79f1597e8515
-- title:
--   Mazur 13 port: goodRing_isLocalization
-- statement:
--   Inverting the vertical nonzero scalars produces the generalized generic fibre coordinate ring.
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13IntegralModelContraction.lean#L101

import Mathlib
import Definitions.Def_MazurN13_L1

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13IntegralModelContraction
open Polynomial
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13IntegralModelContraction.instFactPrimeOfNatNat_fLT
attribute [local instance] MazurProof.N13IntegralModelContraction.integralGoodAlgebra
attribute [local instance] MazurProof.N13IntegralModelContraction.polynomialAlgebra
attribute [local instance] MazurProof.N13IntegralModelContraction.polynomialLocalization

theorem MazurProof.N13IntegralModelContraction.goodRing_isLocalization : IsLocalization verticalScalars GoodRing := by sorry
