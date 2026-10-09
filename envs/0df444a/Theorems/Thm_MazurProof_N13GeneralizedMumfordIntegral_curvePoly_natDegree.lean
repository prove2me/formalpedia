-- Prove2me | Theorems.Thm_MazurProof_N13GeneralizedMumfordIntegral_curvePoly_natDegree
-- name    : MazurProof.N13GeneralizedMumfordIntegral.curvePoly_natDegree
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T03:27:45.788772+00:00
-- url     : https://prove2.me/theorems/9bbb1695-a830-4c76-bb33-ff6f39befe35
-- title:
--   Mazur 13 port: curvePoly_natDegree
-- statement:
--   Supporting lemma `curvePoly_natDegree` (namespace `MazurProof.N13GeneralizedMumfordIntegral`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13GeneralizedMumfordIntegral.lean#L51

import Mathlib
import Definitions.Def_MazurN13_L0

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13GeneralizedMumfordIntegral
open Polynomial
universe u
variable {R : Type u} [CommRing R]

theorem MazurProof.N13GeneralizedMumfordIntegral.curvePoly_natDegree [Nontrivial R] : (curvePoly : R[X][X]).natDegree = 2 := by sorry
