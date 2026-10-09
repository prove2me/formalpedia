-- Prove2me | Theorems.Thm_MazurProof_N13SpecialInfinityGraphDivisor_curveEquationAtRoot
-- name    : MazurProof.N13SpecialInfinityGraphDivisor.curveEquationAtRoot
-- status  : Open
-- author  : @xuanji
-- created : 2026-10-09T08:21:20.742572+00:00
-- url     : https://prove2.me/theorems/5030e254-f425-4987-9c11-2d999c1b30d1
-- title:
--   Mazur 13 port: curveEquationAtRoot
-- statement:
--   Evaluating the graph equation at a horizontal root gives a point on the special infinity chart.
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13SpecialInfinityGraphDivisor.lean#L198

import Mathlib
import Definitions.Def_MazurN13_L4

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13SpecialInfinityGraphDivisor
open Polynomial
open scoped Sym2
attribute [local instance] MazurProof.N13SpecialInfinityGraphDivisor.instFactPrimeOfNatNat_fLT

theorem MazurProof.N13SpecialInfinityGraphDivisor.curveEquationAtRoot (D : SemiMumford) {a : K} (ha : D.u.IsRoot a) : N13GoodModelTwo.InfinityChartEquation a (D.v.eval a) := by sorry
