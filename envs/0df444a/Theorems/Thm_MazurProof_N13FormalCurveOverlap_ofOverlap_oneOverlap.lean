-- Prove2me | Theorems.Thm_MazurProof_N13FormalCurveOverlap_ofOverlap_oneOverlap
-- name    : MazurProof.N13FormalCurveOverlap.ofOverlap_oneOverlap
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T07:14:58.811451+00:00
-- url     : https://prove2.me/theorems/970e3167-71fa-41c2-8577-e3f2d310c74a
-- title:
--   Mazur 13 port: ofOverlap_oneOverlap
-- statement:
--   Supporting lemma `ofOverlap_oneOverlap` (namespace `MazurProof.N13FormalCurveOverlap`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13FormalCurveOverlap.lean#L202

import Mathlib
import Definitions.Def_MazurN13_L4

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13FormalCurveOverlap
open Polynomial
open HahnSeries
open scoped LaurentSeries
attribute [local instance] MazurProof.N13FormalCurveOverlap.instFactPrimeOfNatNat_fLT

theorem MazurProof.N13FormalCurveOverlap.ofOverlap_oneOverlap : ofOverlap (N13FormalLineBundleCech.oneOverlap (R := R₂)) = 1 := by sorry
