-- Prove2me | Theorems.Thm_MazurProof_N13IntegralGraphJacobian_mumfordIdeal_isUnit_of_jacobianBezout
-- name    : MazurProof.N13IntegralGraphJacobian.mumfordIdeal_isUnit_of_jacobianBezout
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T04:55:02.407664+00:00
-- url     : https://prove2.me/theorems/3e72e118-6e04-4cf9-8400-95a314a77c27
-- title:
--   Mazur 13 port: mumfordIdeal_isUnit_of_jacobianBezout
-- statement:
--   A global relative-Jacobian Bézout pair makes every integral smooth Mumford graph invertible by the explicit graph dual frame.
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13IntegralGraphJacobian.lean#L347

import Mathlib
import Definitions.Def_MazurN13_L2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13IntegralGraphJacobian
open Polynomial
open scoped nonZeroDivisors
open N13GeneralizedMumfordIntegral
attribute [local instance] MazurProof.N13IntegralGraphJacobian.instFactPrimeOfNatNat_fLT
attribute [local instance] MazurProof.N13IntegralGraphJacobian.integralRationalAlgebra

theorem MazurProof.N13IntegralGraphJacobian.mumfordIdeal_isUnit_of_jacobianBezout (D : SemiMumford₂) (a b : IntegralRing) (hBez : a * jacobianX + b * jacobianY = 1) : IsUnit ((mumfordIdeal D.u D.v : Ideal IntegralRing) : IntegralFractionalIdeal) := by sorry
