-- Prove2me | Theorems.Thm_MazurProof_SexticMumford_ySubClass_ne_zero
-- name    : MazurProof.SexticMumford.ySubClass_ne_zero
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T03:33:07.007459+00:00
-- url     : https://prove2.me/theorems/e0c18195-073e-4222-b9f3-455772a005dc
-- title:
--   Mazur 13 port: ySubClass_ne_zero
-- statement:
--   Supporting lemma `ySubClass_ne_zero` (namespace `MazurProof.SexticMumford`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/SexticMumfordCantorReduction.lean#L474

import Mathlib
import Definitions.Def_MazurN13_L0

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.SexticMumford
open Polynomial
open scoped nonZeroDivisors
universe u
variable {K : Type u} [Field K]
variable (M : Model K)
attribute [local instance] MazurProof.SexticMumford.instDecidableEq_fLT

theorem MazurProof.SexticMumford.ySubClass_ne_zero (V : K[X]) : ySubClass M V ≠ 0 := by sorry
