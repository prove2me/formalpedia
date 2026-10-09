-- Prove2me | Theorems.Thm_MazurProof_N13IntegralInfinityVerticalGraphJacobian_verticalIdeal_isUnit
-- name    : MazurProof.N13IntegralInfinityVerticalGraphJacobian.verticalIdeal_isUnit
-- status  : Open
-- author  : @xuanji
-- created : 2026-10-09T08:10:27.87012+00:00
-- url     : https://prove2.me/theorems/877cb383-5139-4298-94ee-c279a35b1ede
-- title:
--   Mazur 13 port: verticalIdeal_isUnit
-- statement:
--   Every nondegenerate recovered vertical graph on the ordinary infinity chart is an invertible fractional ideal.
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13IntegralInfinityVerticalGraphJacobian.lean#L286

import Mathlib
import Definitions.Def_MazurN13_L4

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13IntegralInfinityVerticalGraphJacobian
open Polynomial
open scoped nonZeroDivisors
open N13IntegralInfinityGraphJacobian
attribute [local instance] MazurProof.N13IntegralInfinityVerticalGraphJacobian.instFactPrimeOfNatNat_fLT

theorem MazurProof.N13IntegralInfinityVerticalGraphJacobian.verticalIdeal_isUnit (E : VerticalGraph) : IsUnit ((E.ideal : Ideal InfinityCurve) : InfinityFractionalIdeal) := by sorry
