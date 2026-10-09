-- Prove2me | Theorems.Thm_MazurProof_N13InfinityChartMarking_point_map_top_of_nonzero_t
-- name    : MazurProof.N13InfinityChartMarking.point_map_top_of_nonzero_t
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T04:46:38.458307+00:00
-- url     : https://prove2.me/theorems/8bf93254-9b4c-4c77-93d5-cd4da9f51759
-- title:
--   Mazur 13 port: point_map_top_of_nonzero_t
-- statement:
--   Supporting lemma `point_map_top_of_nonzero_t` (namespace `MazurProof.N13InfinityChartMarking`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13InfinityChartMarking.lean#L314

import Mathlib
import Definitions.Def_MazurN13_L2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13InfinityChartMarking
open Polynomial
attribute [local instance] MazurProof.N13InfinityChartMarking.instFactPrimeOfNatNat_fLT

theorem MazurProof.N13InfinityChartMarking.point_map_top_of_nonzero_t (f : B →+* QP) (hf : ∀ p : N13IntegralInfinityChart.Base, f (N13IntegralInfinityPointSpread.xClassHom p) = N13TwoAdicInfinityCompatibility.powerMap (N13IntegralInfinityChart.baseToPower p)) (p : N13IntegralInfinityPointSpread.IntegralInfinityPoint) (hp : p.1.1 ≠ 0) : Ideal.map f (N13IntegralInfinityPointSpread.pointIdeal p) = ⊤ := by sorry
