-- Prove2me | Theorems.Thm_MazurProof_N13LowDegreeKummerHom_lowFakeClass_add_of_class_add
-- name    : MazurProof.N13LowDegreeKummerHom.lowFakeClass_add_of_class_add
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T05:00:20.615986+00:00
-- url     : https://prove2.me/theorems/5ec20dda-5466-45af-85d0-2276b54c80d8
-- title:
--   Mazur 13 port: lowFakeClass_add_of_class_add
-- statement:
--   Addition of original oriented classes gives multiplication of the affine Mumford ideals modulo a principal ideal, hence addition of fake values.
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13LowDegreeKummerHom.lean#L136

import Mathlib
import Definitions.Def_MazurN13_L2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13LowDegreeKummerHom
open SexticMumford

theorem MazurProof.N13LowDegreeKummerHom.lowFakeClass_add_of_class_add (D₁ D₂ D₃ : LowRep) (h : lowClass D₃ = lowClass D₁ + lowClass D₂) : lowFakeClass D₃ = lowFakeClass D₁ + lowFakeClass D₂ := by sorry
