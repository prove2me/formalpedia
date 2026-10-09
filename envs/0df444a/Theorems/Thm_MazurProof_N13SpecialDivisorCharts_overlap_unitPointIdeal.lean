-- Prove2me | Theorems.Thm_MazurProof_N13SpecialDivisorCharts_overlap_unitPointIdeal
-- name    : MazurProof.N13SpecialDivisorCharts.overlap_unitPointIdeal
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T05:31:36.613183+00:00
-- url     : https://prove2.me/theorems/28d509ef-e4a5-4d3c-9878-aeed92a77f88
-- title:
--   Mazur 13 port: overlap_unitPointIdeal
-- statement:
--   On the overlap, the point ideals written in the coordinates `x=t⁻¹` and `y=x³v` agree at `x=t=1`. The first generators differ by the units `x` and `t`. Once those generators are identified, the difference between the second generators is a multiple of `x³-1` or `t³-1`, respectively.
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13SpecialDivisorCharts.lean#L125

import Mathlib
import Definitions.Def_MazurN13_L2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13SpecialDivisorCharts
open Polynomial
open scoped Sym2
attribute [local instance] MazurProof.N13SpecialDivisorCharts.instFactPrimeOfNatNat_fLT

theorem MazurProof.N13SpecialDivisorCharts.overlap_unitPointIdeal (c : SpecialOverlap) : Ideal.span {N13SpecialCurveOverlap.xOverlap - 1, N13SpecialCurveOverlap.xOverlap ^ 3 * N13SpecialCurveOverlap.vOverlap - c} = Ideal.span {N13SpecialCurveOverlap.tOverlap - 1, N13SpecialCurveOverlap.vOverlap - c} := by sorry
