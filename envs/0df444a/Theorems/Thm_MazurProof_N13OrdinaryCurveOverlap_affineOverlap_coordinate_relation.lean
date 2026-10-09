-- Prove2me | Theorems.Thm_MazurProof_N13OrdinaryCurveOverlap_affineOverlap_coordinate_relation
-- name    : MazurProof.N13OrdinaryCurveOverlap.affineOverlap_coordinate_relation
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T03:45:49.428862+00:00
-- url     : https://prove2.me/theorems/ded2aca3-510b-42dc-87db-0418922214c8
-- title:
--   Mazur 13 port: affineOverlap_coordinate_relation
-- statement:
--   Supporting lemma `affineOverlap_coordinate_relation` (namespace `MazurProof.N13OrdinaryCurveOverlap`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13OrdinaryCurveOverlap.lean#L266

import Mathlib
import Definitions.Def_MazurN13_L1

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13OrdinaryCurveOverlap
open Polynomial
attribute [local instance] MazurProof.N13OrdinaryCurveOverlap.instFactPrimeOfNatNat_fLT

theorem MazurProof.N13OrdinaryCurveOverlap.affineOverlap_coordinate_relation : yAffineOverlap ^ 2 + (xAffineOverlap ^ 3 + xAffineOverlap + 1) * yAffineOverlap = xAffineOverlap ^ 5 + xAffineOverlap ^ 4 := by sorry
