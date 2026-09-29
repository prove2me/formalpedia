-- Prove2me | Theorems.Thm_ModularCurve_coeff_slotSubst_tateUnivX_eq_zero_of_lt_min_and_coeff_eq_and_order_eq_min
-- name    : ModularCurve.coeff_slotSubst_tateUnivX_eq_zero_of_lt_min_and_coeff_eq_and_order_eq_min
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/cb9dc7bf-beb6-55e9-bcdd-0bfd2a3c27ad
-- title:
--   Order of the slot-substituted universal Tate x-series
-- statement:
--   Let $K$ be a commutative ring, $p$ and $j$ natural numbers with $0 < j$ and $j < p$, and $c \in K^{\times}$. Write $F =$ `slotSubst K p c j tateUnivX` $\in K[[X]]$ for the one-variable power series obtained by substituting, in the two-variable series `tateUnivX` over $\mathbb{Z}$ — whose coefficient at an exponent vector $e \colon \mathrm{Fin}\,2 \to \mathbb{N}$ is $-2\sum_{d \mid e_1} d$ when $e_0 = e_1$, is $e_0 - e_1$ or $0$ according as $e_0 - e_1$ divides $e_1$ or not when $e_1 < e_0$, and is $e_1 - e_0$ or $0$ according as $e_1 - e_0$ divides $e_1$ or not when $e_0 \le e_1$ — the family of series $c\,X^{j}$ and $c^{-1}X^{\,p-j}$ for the two variables. The assertion is a conjunction of four statements: the coefficient of $X^{n}$ in $F$ vanishes for every $n < \min(j, p-j)$; if $j < p-j$ then the coefficient of $X^{j}$ equals $c$; if $p-j < j$ then the coefficient of $X^{\,p-j}$ equals $c^{-1}$; and if $K$ is nontrivial and $2j \ne p$ then the order of $F$ equals $\min(j, p-j)$.
--
--   The series $F$ is the abscissa of the point with Tate parameter $u = c\,q^{j}$ on the Tate curve with parameter $q^{p}$, and the statement records that its $q$-adic order is $\min(j, p-j)$ with leading coefficient the unit $c$ or $c^{-1}$. It is used in the construction of power series whose reduction is nonzero and which represent differences of toric and non-toric points on the modular curve, and in the accompanying study of level automorphisms at an auxiliary level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coeff_slotSubst_tateUnivX_eq_zero_of_lt_min_and_coeff_eq_and_order_eq_min.lean

import Definitions.Def_ModularCurve_TateSlots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.coeff_slotSubst_tateUnivX_eq_zero_of_lt_min_and_coeff_eq_and_order_eq_min
    {K : Type*} [CommRing K] (p : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    (∀ n : ℕ, n < min j (p - j) → PowerSeries.coeff n (slotSubst K p c j tateUnivX) = 0) ∧
    (j < p - j → PowerSeries.coeff j (slotSubst K p c j tateUnivX) = (c : K)) ∧
    (p - j < j → PowerSeries.coeff (p - j) (slotSubst K p c j tateUnivX) = ((c⁻¹ : Kˣ) : K)) ∧
    (Nontrivial K → 2 * j ≠ p → PowerSeries.order (slotSubst K p c j tateUnivX) = (min j (p - j) : ℕ)) := by sorry
