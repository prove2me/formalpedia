-- Prove2me | Theorems.Thm_MazurProof_N13SpecialInfinityBranchJets_root_eval
-- name    : MazurProof.N13SpecialInfinityBranchJets.root_eval
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T05:34:21.147987+00:00
-- url     : https://prove2.me/theorems/31a98cb0-f5ee-4bc6-b962-799f16d6b511
-- title:
--   Mazur 13 port: root_eval
-- statement:
--   Supporting lemma `root_eval` (namespace `MazurProof.N13SpecialInfinityBranchJets`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13SpecialInfinityBranchJets.lean#L68

import Mathlib
import Definitions.Def_MazurN13_L2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13SpecialInfinityBranchJets
open Polynomial
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT

theorem MazurProof.N13SpecialInfinityBranchJets.root_eval (r : P) (hr : r ^ 2 + h * r - rhs = 0) : N13SpecialInfinityChart.curvePoly.eval₂ beta r = 0 := by sorry
