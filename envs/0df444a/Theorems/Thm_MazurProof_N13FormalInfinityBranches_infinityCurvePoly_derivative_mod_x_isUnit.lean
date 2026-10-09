-- Prove2me | Theorems.Thm_MazurProof_N13FormalInfinityBranches_infinityCurvePoly_derivative_mod_x_isUnit
-- name    : MazurProof.N13FormalInfinityBranches.infinityCurvePoly_derivative_mod_x_isUnit
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T07:26:01.047072+00:00
-- url     : https://prove2.me/theorems/d22a9305-b8b3-4cf4-9a17-038d601206e4
-- title:
--   Mazur 13 port: infinityCurvePoly_derivative_mod_x_isUnit
-- statement:
--   Supporting lemma `infinityCurvePoly_derivative_mod_x_isUnit` (namespace `MazurProof.N13FormalInfinityBranches`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13FormalInfinityBranches.lean#L65

import Mathlib
import Definitions.Def_MazurN13_L4

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13FormalInfinityBranches
open Polynomial
attribute [local instance] MazurProof.N13FormalInfinityBranches.instFactPrimeOfNatNat_fLT
attribute [local instance] MazurProof.N13FormalInfinityBranches.instIsAdicCompletePowerXIdeal

theorem MazurProof.N13FormalInfinityBranches.infinityCurvePoly_derivative_mod_x_isUnit : IsUnit (Ideal.Quotient.mk xIdeal (N13FormalInfinityChart.infinityCurvePoly.derivative.eval 0)) := by sorry
