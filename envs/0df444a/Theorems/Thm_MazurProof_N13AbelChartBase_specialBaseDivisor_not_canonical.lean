-- Prove2me | Theorems.Thm_MazurProof_N13AbelChartBase_specialBaseDivisor_not_canonical
-- name    : MazurProof.N13AbelChartBase.specialBaseDivisor_not_canonical
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T03:44:57.084985+00:00
-- url     : https://prove2.me/theorems/4383cf1a-3f10-438a-bb90-6fb7e63748de
-- title:
--   Mazur 13 port: specialBaseDivisor_not_canonical
-- statement:
--   The base divisor is outside the canonical hyperelliptic pencil. The proof only compares sheet coordinates; it does not enumerate curve points.
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13AbelChartBase.lean#L80

import Mathlib
import Definitions.Def_MazurN13_L1

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13AbelChartBase
open Polynomial
open N13AbelFiberTwoModel
open N13SymmetricSquareTwo
attribute [local instance] MazurProof.N13AbelChartBase.instFactPrimeOfNatNat_fLT

theorem MazurProof.N13AbelChartBase.specialBaseDivisor_not_canonical : ¬IsCanonical specialBaseDivisor := by sorry
