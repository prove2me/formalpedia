-- Prove2me | Theorems.Thm_MazurProof_N13SpecialQuotientBasis_specialData_u_natDegree
-- name    : MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T03:45:07.045667+00:00
-- url     : https://prove2.me/theorems/bc89135f-11c8-4f8a-a210-e7a6a795d44e
-- title:
--   Mazur 13 port: specialData_u_natDegree
-- statement:
--   Supporting lemma `specialData_u_natDegree` (namespace `MazurProof.N13SpecialQuotientBasis`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13SpecialQuotientBasis.lean#L51

import Mathlib
import Definitions.Def_MazurN13_L1

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13SpecialQuotientBasis
open Module
open Polynomial

theorem MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree : specialData.u.natDegree = 2 := by sorry
