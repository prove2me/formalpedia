-- Prove2me | Theorems.Thm_MazurProof_N13GoodSexticCoordinateEquiv_goodYInSextic_root
-- name    : MazurProof.N13GoodSexticCoordinateEquiv.goodYInSextic_root
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T03:51:02.307277+00:00
-- url     : https://prove2.me/theorems/e69305b8-3049-4332-8b28-f2ec4cceff77
-- title:
--   Mazur 13 port: goodYInSextic_root
-- statement:
--   Supporting lemma `goodYInSextic_root` (namespace `MazurProof.N13GoodSexticCoordinateEquiv`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13GoodSexticCoordinateEquiv.lean#L85

import Mathlib
import Definitions.Def_MazurN13_L1

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13GoodSexticCoordinateEquiv
open Polynomial
universe u
variable {K : Type u} [Field K] [CharZero K]

theorem MazurProof.N13GoodSexticCoordinateEquiv.goodYInSextic_root : (N13GeneralizedMumfordIntegral.curvePoly (R := K)).eval₂ (sexticXHom (K := K)) (goodYInSextic (K := K)) = 0 := by sorry
