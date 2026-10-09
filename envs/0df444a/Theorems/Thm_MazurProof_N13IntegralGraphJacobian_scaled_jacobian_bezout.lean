-- Prove2me | Theorems.Thm_MazurProof_N13IntegralGraphJacobian_scaled_jacobian_bezout
-- name    : MazurProof.N13IntegralGraphJacobian.scaled_jacobian_bezout
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T03:30:15.923038+00:00
-- url     : https://prove2.me/theorems/3d6561b5-e334-4854-b8a2-b601b62bd966
-- title:
--   Mazur 13 port: scaled_jacobian_bezout
-- statement:
--   The integral resultant certificate for the two relative Jacobian rows. It comes from the univariate Euclidean identity between `h² + 4 * rhs` and `h' * h + 2 * rhs'`; its right-hand side is the optimal odd scalar `13`.
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13IntegralGraphJacobian.lean#L162

import Mathlib
import Definitions.Def_MazurN13_L0

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13IntegralGraphJacobian
open Polynomial
open scoped nonZeroDivisors
open N13GeneralizedMumfordIntegral
attribute [local instance] MazurProof.N13IntegralGraphJacobian.instFactPrimeOfNatNat_fLT

theorem MazurProof.N13IntegralGraphJacobian.scaled_jacobian_bezout : bezoutA * jacobianX + bezoutB * jacobianY = (13 : IntegralRing) := by sorry
