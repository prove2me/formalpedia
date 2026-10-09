-- Prove2me | Theorems.Thm_MazurProof_N13GoodSexticMumfordTransport_sextic_mumfordIdeal_eq_of_dvd_sub
-- name    : MazurProof.N13GoodSexticMumfordTransport.sextic_mumfordIdeal_eq_of_dvd_sub
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T03:45:37.602335+00:00
-- url     : https://prove2.me/theorems/2815e158-9388-4005-9ba1-e257459fee72
-- title:
--   Mazur 13 port: sextic_mumfordIdeal_eq_of_dvd_sub
-- statement:
--   Congruent graph polynomials define the same sextic graph ideal.
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13GoodSexticMumfordTransport.lean#L145

import Mathlib
import Definitions.Def_MazurN13_L1

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13GoodSexticMumfordTransport
open Polynomial
open N13GoodSexticCoordinateEquiv
universe u
variable {K : Type u} [Field K] [CharZero K]

theorem MazurProof.N13GoodSexticMumfordTransport.sextic_mumfordIdeal_eq_of_dvd_sub (u v w : K[X]) (hvw : u ∣ v - w) : SexticMumford.mumfordIdeal (N13GoodSexticCoordinateEquiv.M (K := K)) u v = SexticMumford.mumfordIdeal (N13GoodSexticCoordinateEquiv.M (K := K)) u w := by sorry
