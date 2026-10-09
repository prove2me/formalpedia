-- Prove2me | Theorems.Thm_MazurProof_N13SpecialCuspReduction_cuspOfCoordinate_cuspCoordinate
-- name    : MazurProof.N13SpecialCuspReduction.cuspOfCoordinate_cuspCoordinate
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T05:30:24.663867+00:00
-- url     : https://prove2.me/theorems/917e0b28-e861-45d7-a0f0-694fc3ba735a
-- title:
--   Mazur 13 port: cuspOfCoordinate_cuspCoordinate
-- statement:
--   Supporting lemma `cuspOfCoordinate_cuspCoordinate` (namespace `MazurProof.N13SpecialCuspReduction`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13SpecialCuspReduction.lean#L54

import Mathlib
import Definitions.Def_MazurN13_L2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13SpecialCuspReduction
open N13AbelFiberTwoModel

theorem MazurProof.N13SpecialCuspReduction.cuspOfCoordinate_cuspCoordinate (c : Cusp13) : cuspOfCoordinate (cuspCoordinate c) = c := by sorry
