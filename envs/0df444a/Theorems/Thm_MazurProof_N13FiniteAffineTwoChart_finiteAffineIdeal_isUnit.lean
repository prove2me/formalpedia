-- Prove2me | Theorems.Thm_MazurProof_N13FiniteAffineTwoChart_finiteAffineIdeal_isUnit
-- name    : MazurProof.N13FiniteAffineTwoChart.finiteAffineIdeal_isUnit
-- status  : Open
-- author  : @xuanji
-- created : 2026-10-09T04:19:51.086297+00:00
-- url     : https://prove2.me/theorems/c691e154-4235-469f-9333-2891c6eb4655
-- title:
--   Mazur 13 port: finiteAffineIdeal_isUnit
-- statement:
--   Finite quadratic support makes the canonical affine lattice invertible.
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13FiniteAffineTwoChart.lean#L99

import Mathlib
import Definitions.Def_MazurN13_L2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13FiniteAffineTwoChart
open Polynomial
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13FiniteAffineTwoChart.instFactPrimeOfNatNat_fLT

theorem MazurProof.N13FiniteAffineTwoChart.finiteAffineIdeal_isUnit (D : SexticMumford.SemiMumford Model) (hdeg : D.u.natDegree = 2) (hfinite : Module.Finite R₂ (AffineCurve ⧸ finiteAffineIdeal D)) : IsUnit (finiteAffineIdeal D : AffineFractionalIdeal) := by sorry
