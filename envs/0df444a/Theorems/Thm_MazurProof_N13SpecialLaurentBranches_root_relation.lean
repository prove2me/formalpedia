-- Prove2me | Theorems.Thm_MazurProof_N13SpecialLaurentBranches_root_relation
-- name    : MazurProof.N13SpecialLaurentBranches.root_relation
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T05:38:09.329367+00:00
-- url     : https://prove2.me/theorems/4c1ace2e-8ba8-4e98-9334-28a1a815e22e
-- title:
--   Mazur 13 port: root_relation
-- statement:
--   Supporting lemma `root_relation` (namespace `MazurProof.N13SpecialLaurentBranches`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13SpecialLaurentBranches.lean#L39

import Mathlib
import Definitions.Def_MazurN13_L2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13SpecialLaurentBranches
open Polynomial
open scoped LaurentSeries

theorem MazurProof.N13SpecialLaurentBranches.root_relation (r : P) (hr : r ^ 2 + N13SpecialInfinityBranchJets.h * r - N13SpecialInfinityBranchJets.rhs = 0) : N13GoodCoordinateRingTwo.curvePoly.eval₂ base (t⁻¹ ^ 3 * includeSeries r) = 0 := by sorry
