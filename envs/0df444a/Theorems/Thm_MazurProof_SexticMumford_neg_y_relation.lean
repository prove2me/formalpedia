-- Prove2me | Theorems.Thm_MazurProof_SexticMumford_neg_y_relation
-- name    : MazurProof.SexticMumford.neg_y_relation
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T03:33:13.168984+00:00
-- url     : https://prove2.me/theorems/a4ea6a33-974f-40ce-be7e-f10bd36b5f1c
-- title:
--   Mazur 13 port: neg_y_relation
-- statement:
--   Supporting lemma `neg_y_relation` (namespace `MazurProof.SexticMumford`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/SexticMumfordBasis.lean#L156

import Mathlib
import Definitions.Def_MazurN13_L0

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.SexticMumford
open Polynomial
universe u
variable {K : Type u} [Field K]
variable (M : Model K)

theorem MazurProof.SexticMumford.neg_y_relation : (curvePoly M).eval₂ (AdjoinRoot.of (curvePoly M)) (-(yClass M)) = 0 := by sorry
