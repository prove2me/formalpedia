-- Prove2me | Theorems.Thm_MazurProof_N13SpecialGraphDivisor_graphDivisor_eq_special_of_mumfordIdeal_eq
-- name    : MazurProof.N13SpecialGraphDivisor.graphDivisor_eq_special_of_mumfordIdeal_eq
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T05:32:48.076955+00:00
-- url     : https://prove2.me/theorems/a3d5f09f-4263-446d-9834-48f6d850db44
-- title:
--   Mazur 13 port: graphDivisor_eq_special_of_mumfordIdeal_eq
-- statement:
--   The literal special graph ideal determines the selected effective divisor. The proof recovers the two roots and evaluates the graph there; it does not enumerate the special curve.
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13SpecialGraphDivisor.lean#L374

import Mathlib
import Definitions.Def_MazurN13_L2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13SpecialGraphDivisor
open Polynomial
open scoped Sym2
open MazurProof.N13GoodCoordinateRingTwo
attribute [local instance] MazurProof.N13SpecialGraphDivisor.instFactPrimeOfNatNat_fLT

theorem MazurProof.N13SpecialGraphDivisor.graphDivisor_eq_special_of_mumfordIdeal_eq (D : SemiMumford) (hdeg : D.u.natDegree = 2) (hideal : mumfordIdeal D.u D.v = N13SpecialQuotientBasis.specialIdeal) : graphDivisor D hdeg = N13AbelChartBase.specialBaseDivisor := by sorry
