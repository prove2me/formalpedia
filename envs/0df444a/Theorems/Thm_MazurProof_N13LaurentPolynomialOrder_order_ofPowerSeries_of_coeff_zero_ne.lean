-- Prove2me | Theorems.Thm_MazurProof_N13LaurentPolynomialOrder_order_ofPowerSeries_of_coeff_zero_ne
-- name    : MazurProof.N13LaurentPolynomialOrder.order_ofPowerSeries_of_coeff_zero_ne
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T03:24:54.827767+00:00
-- url     : https://prove2.me/theorems/e64bc899-2c31-415d-873b-b51a472c04e0
-- title:
--   Mazur 13 port: order_ofPowerSeries_of_coeff_zero_ne
-- statement:
--   Supporting lemma `order_ofPowerSeries_of_coeff_zero_ne` (namespace `MazurProof.N13LaurentPolynomialOrder`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13LaurentPolynomialOrder.lean#L67

import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial
open scoped LaurentSeries PowerSeries
universe u
variable (K : Type u) [Field K]

theorem MazurProof.N13LaurentPolynomialOrder.order_ofPowerSeries_of_coeff_zero_ne (p : K[X]) (hp : p.coeff 0 ≠ 0) : (HahnSeries.ofPowerSeries ℤ K p).order = 0 := by sorry
