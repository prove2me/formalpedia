-- Prove2me | Theorems.Thm_MazurProof_N13LaurentPolynomialOrder_eval_parameter_eq_ofPowerSeries
-- name    : MazurProof.N13LaurentPolynomialOrder.eval_parameter_eq_ofPowerSeries
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T03:30:14.400612+00:00
-- url     : https://prove2.me/theorems/a8a19f23-ef93-4b6c-ab7e-94ff8dc53b21
-- title:
--   Mazur 13 port: eval_parameter_eq_ofPowerSeries
-- statement:
--   Supporting lemma `eval_parameter_eq_ofPowerSeries` (namespace `MazurProof.N13LaurentPolynomialOrder`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13LaurentPolynomialOrder.lean#L51

import Mathlib
import Definitions.Def_MazurN13_L0

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13LaurentPolynomialOrder
open Polynomial
open scoped LaurentSeries PowerSeries
universe u
variable (K : Type u) [Field K]

theorem MazurProof.N13LaurentPolynomialOrder.eval_parameter_eq_ofPowerSeries (p : K[X]) : p.eval₂ (algebraMap K (LaurentSeries K)) (parameter K) = HahnSeries.ofPowerSeries ℤ K p := by sorry
