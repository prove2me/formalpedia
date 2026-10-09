-- Prove2me | Theorems.Thm_MazurProof_N13EscapingPointPicardRealization_affinePointIdeal_scalarSaturated
-- name    : MazurProof.N13EscapingPointPicardRealization.affinePointIdeal_scalarSaturated
-- status  : Open
-- author  : @xuanji
-- created : 2026-10-09T04:24:04.920875+00:00
-- url     : https://prove2.me/theorems/81f225d0-b208-4494-812f-da835af0dd80
-- title:
--   Mazur 13 port: affinePointIdeal_scalarSaturated
-- statement:
--   The affine closure of an integral infinity-chart point is saturated by every nonzero two-adic scalar. The infinity point ideal is a monic graph, hence saturated. Saturation survives localization to the overlap, and `affinePointIdeal_xUnitMod` shows that contracting from the overlap recovers the original affine ideal.
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13EscapingPointPicardRealization.lean#L74

import Mathlib
import Definitions.Def_MazurN13_L2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13EscapingPointPicardRealization
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13EscapingPointPicardRealization.instFactPrimeOfNatNat_fLT

theorem MazurProof.N13EscapingPointPicardRealization.affinePointIdeal_scalarSaturated (P : N13IntegralInfinityPointSpread.IntegralInfinityPoint) (r : N13IntegralModelContraction.R₂) (hr : r ≠ 0) (z : N13IntegralModelContraction.IntegralRing) (hz : algebraMap N13IntegralModelContraction.R₂ N13IntegralModelContraction.IntegralRing r * z ∈ N13IntegralInfinityPointSpread.affinePointIdeal P) : z ∈ N13IntegralInfinityPointSpread.affinePointIdeal P := by sorry
