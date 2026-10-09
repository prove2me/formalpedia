-- Prove2me | Theorems.Thm_MazurProof_N13GoodSexticCoordinateEquiv_sexticYInGood_root
-- name    : MazurProof.N13GoodSexticCoordinateEquiv.sexticYInGood_root
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T03:50:26.62898+00:00
-- url     : https://prove2.me/theorems/deab4c2e-7d5f-41d5-9549-9a9aa14fc9be
-- title:
--   Mazur 13 port: sexticYInGood_root
-- statement:
--   Supporting lemma `sexticYInGood_root` (namespace `MazurProof.N13GoodSexticCoordinateEquiv`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13GoodSexticCoordinateEquiv.lean#L129

import Mathlib
import Definitions.Def_MazurN13_L1

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13GoodSexticCoordinateEquiv
open Polynomial
universe u
variable {K : Type u} [Field K] [CharZero K]

theorem MazurProof.N13GoodSexticCoordinateEquiv.sexticYInGood_root : (SexticMumford.curvePoly (M (K := K))).eval₂ (goodXHom (K := K)) (sexticYInGood (K := K)) = 0 := by sorry
