-- Prove2me | Theorems.Thm_MazurProof_N13SpecialGraphDivisor_u_eq_base_and_dvd_v_of_graphDivisor_eq
-- name    : MazurProof.N13SpecialGraphDivisor.u_eq_base_and_dvd_v_of_graphDivisor_eq
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T05:33:46.596261+00:00
-- url     : https://prove2.me/theorems/44050941-48d7-4a6b-aa4f-56820f3af6d1
-- title:
--   Mazur 13 port: u_eq_base_and_dvd_v_of_graphDivisor_eq
-- statement:
--   Supporting lemma `u_eq_base_and_dvd_v_of_graphDivisor_eq` (namespace `MazurProof.N13SpecialGraphDivisor`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13SpecialGraphDivisor.lean#L246

import Mathlib
import Definitions.Def_MazurN13_L2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13SpecialGraphDivisor
open Polynomial
open scoped Sym2
open MazurProof.N13GoodCoordinateRingTwo
attribute [local instance] MazurProof.N13SpecialGraphDivisor.instFactPrimeOfNatNat_fLT

theorem MazurProof.N13SpecialGraphDivisor.u_eq_base_and_dvd_v_of_graphDivisor_eq (D : SemiMumford) (hdeg : D.u.natDegree = 2) (hgraph : graphDivisor D hdeg = N13AbelChartBase.specialBaseDivisor) : D.u = (X ^ 2 + X : K[X]) ∧ D.u ∣ D.v := by sorry
