-- Prove2me | Theorems.Thm_MazurProof_SexticMumford_ker_mumfordEval
-- name    : MazurProof.SexticMumford.ker_mumfordEval
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T05:45:25.969023+00:00
-- url     : https://prove2.me/theorems/bb54b7ee-3252-4e69-8d53-c27a859422d2
-- title:
--   Mazur 13 port: ker_mumfordEval
-- statement:
--   Supporting lemma `ker_mumfordEval` (namespace `MazurProof.SexticMumford`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/SexticMumfordIdeal.lean#L84

import Mathlib
import Definitions.Def_MazurN13_L2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.SexticMumford
open Polynomial
universe u
variable {K : Type u} [Field K]
variable (M : Model K)

theorem MazurProof.SexticMumford.ker_mumfordEval (D : SemiMumford M) : RingHom.ker (mumfordEval M D) = mumfordIdeal M D.u D.v := by sorry
