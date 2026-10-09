-- Prove2me | Theorems.Thm_MazurProof_N13OrdinaryCurveOverlap_infinityOverlap_coordinate_relation
-- name    : MazurProof.N13OrdinaryCurveOverlap.infinityOverlap_coordinate_relation
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T05:13:56.678546+00:00
-- url     : https://prove2.me/theorems/91cfcc82-fc18-41cd-b7d6-3b2ab06bc1c2
-- title:
--   Mazur 13 port: infinityOverlap_coordinate_relation
-- statement:
--   Supporting lemma `infinityOverlap_coordinate_relation` (namespace `MazurProof.N13OrdinaryCurveOverlap`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13OrdinaryCurveOverlap.lean#L106

import Mathlib
import Definitions.Def_MazurN13_L2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13OrdinaryCurveOverlap
open Polynomial
attribute [local instance] MazurProof.N13OrdinaryCurveOverlap.instFactPrimeOfNatNat_fLT

theorem MazurProof.N13OrdinaryCurveOverlap.infinityOverlap_coordinate_relation : vOverlap ^ 2 + (1 + tOverlap ^ 2 + tOverlap ^ 3) * vOverlap = tOverlap + tOverlap ^ 2 := by sorry
