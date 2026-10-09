-- Prove2me | Theorems.Thm_MazurProof_N13SpecialCurveOverlap_infinityCoeffMap_hPoly
-- name    : MazurProof.N13SpecialCurveOverlap.infinityCoeffMap_hPoly
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T05:25:39.222028+00:00
-- url     : https://prove2.me/theorems/c832a2e6-b1de-4449-a19d-ebbe8d6a32c7
-- title:
--   Mazur 13 port: infinityCoeffMap_hPoly
-- statement:
--   Supporting lemma `infinityCoeffMap_hPoly` (namespace `MazurProof.N13SpecialCurveOverlap`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13SpecialCurveOverlap.lean#L270

import Mathlib
import Definitions.Def_MazurN13_L2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13SpecialCurveOverlap
open Polynomial
attribute [local instance] MazurProof.N13SpecialCurveOverlap.instFactPrimeOfNatNat_fLT

theorem MazurProof.N13SpecialCurveOverlap.infinityCoeffMap_hPoly : infinityCoeffMap N13SpecialInfinityChart.hPoly = 1 + tAffineOverlap ^ 2 + tAffineOverlap ^ 3 := by sorry
