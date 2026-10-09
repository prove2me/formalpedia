-- Prove2me | Theorems.Thm_MazurProof_N13LaurentPolynomialOrder_evalAtInfinity_eq_reverse_mul
-- name    : MazurProof.N13LaurentPolynomialOrder.evalAtInfinity_eq_reverse_mul
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T03:30:24.687162+00:00
-- url     : https://prove2.me/theorems/e03cef32-d27c-4707-84a5-14797d420406
-- title:
--   Mazur 13 port: evalAtInfinity_eq_reverse_mul
-- statement:
--   Supporting lemma `evalAtInfinity_eq_reverse_mul` (namespace `MazurProof.N13LaurentPolynomialOrder`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13LaurentPolynomialOrder.lean#L94

import Mathlib
import Definitions.Def_MazurN13_L0

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13LaurentPolynomialOrder
open Polynomial
open scoped LaurentSeries PowerSeries
universe u
variable (K : Type u) [Field K]

theorem MazurProof.N13LaurentPolynomialOrder.evalAtInfinity_eq_reverse_mul (p : K[X]) : evalAtInfinity K p = p.reverse.eval₂ (algebraMap K (LaurentSeries K)) (parameter K) * (parameter K)⁻¹ ^ p.natDegree := by sorry
