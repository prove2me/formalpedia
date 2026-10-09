-- Prove2me | Theorems.Thm_MazurProof_N13GoodSexticCoordinateEquiv_toGood_comp_toSextic
-- name    : MazurProof.N13GoodSexticCoordinateEquiv.toGood_comp_toSextic
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T04:44:16.390762+00:00
-- url     : https://prove2.me/theorems/b04800d3-62ba-467a-9794-8f1ce0c1d495
-- title:
--   Mazur 13 port: toGood_comp_toSextic
-- statement:
--   Supporting lemma `toGood_comp_toSextic` (namespace `MazurProof.N13GoodSexticCoordinateEquiv`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13GoodSexticCoordinateEquiv.lean#L225

import Mathlib
import Definitions.Def_MazurN13_L2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13GoodSexticCoordinateEquiv
open Polynomial
universe u
variable {K : Type u} [Field K] [CharZero K]

theorem MazurProof.N13GoodSexticCoordinateEquiv.toGood_comp_toSextic : (toGood (K := K)).comp (toSextic (K := K)) = RingHom.id (GoodRing (K := K)) := by sorry
