-- Prove2me | Theorems.Thm_MazurProof_N13FormalCurveOverlap_ofOverlap_mul
-- name    : MazurProof.N13FormalCurveOverlap.ofOverlap_mul
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T07:15:56.030883+00:00
-- url     : https://prove2.me/theorems/d8697f87-455a-4139-ba0e-7d02fb3eb0f0
-- title:
--   Mazur 13 port: ofOverlap_mul
-- statement:
--   Pair multiplication is exactly multiplication in the actual quadratic formal-curve algebra.
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13FormalCurveOverlap.lean#L223

import Mathlib
import Definitions.Def_MazurN13_L4

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13FormalCurveOverlap
open Polynomial
open HahnSeries
open scoped LaurentSeries
attribute [local instance] MazurProof.N13FormalCurveOverlap.instFactPrimeOfNatNat_fLT

theorem MazurProof.N13FormalCurveOverlap.ofOverlap_mul (z w : Overlap) : ofOverlap (N13FormalLineBundleCech.mulOverlap z w) = ofOverlap z * ofOverlap w := by sorry
