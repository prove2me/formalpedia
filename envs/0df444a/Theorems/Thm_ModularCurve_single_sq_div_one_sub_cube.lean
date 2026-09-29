-- Prove2me | Theorems.Thm_ModularCurve_single_sq_div_one_sub_cube
-- name    : ModularCurve.single_sq_div_one_sub_cube
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/cb87dbef-32cd-5a71-ad4f-b19e8c6ff802
-- title:
--   Closed form for w²/(1-w)³ at a monomial in K((q))
-- statement:
--   Let $K$ be a field, let $j$ be a natural number with $j>0$, and let $c\in K$. Work in the field of Laurent series $K((q))$, realised as Hahn series over $\mathbb{Z}$ with coefficients in $K$, and write $w=\mathrm{single}_{j}(c)$ for the Hahn series supported in the single degree $j$ with coefficient $c$ there, i.e. $w=cq^{j}$. The assertion is the identity
--   $$\frac{w^{2}}{(1-w)^{3}}=\sum_{n\ge 0}a_{n}q^{n},\qquad a_{n}=\begin{cases}\binom{n/j}{2}\,c^{\,n/j}&\text{if }j\mid n,\\ 0&\text{otherwise,}\end{cases}$$
--   where the right-hand side is the image under `HahnSeries.ofPowerSeries` of the formal power series with these coefficients, the quotient $n/j$ being natural-number division and $\binom{m}{2}$ the natural binomial coefficient mapped into $K$. Equivalently, the left-hand side is $\sum_{m\ge 0}\binom{m}{2}c^{m}q^{jm}$. Division is division in the Laurent series field; the hypothesis $j>0$ guarantees that $1-cq^{j}$ has constant term $1$, hence is invertible, and that the right-hand side is a power series.
--
--   This is the generating function identity $\sum_{m\ge0}\binom{m}{2}w^{m}=w^{2}/(1-w)^{3}$ specialised to the monomial $w=cq^{j}$, the companion of $\sum_{m\ge0}mw^{m}=w/(1-w)^{2}$. It supplies the $q$-expansion of the leading term $u^{2}/(1-u)^{3}$ occurring in the $y$-coordinate of points of the Tate curve, and is used in [`ModularCurve.tateUniv_equation`](thm.html#ModularCurve.tateUniv_equation) and [`ModularCurve.toricPoint_equation`](thm.html#ModularCurve.toricPoint_equation).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_single_sq_div_one_sub_cube.lean

import Mathlib.RingTheory.LaurentSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.single_sq_div_one_sub_cube (K : Type*) [Field K] (j : ℕ) (hj : 0 < j) (c : K) :
    HahnSeries.single (j : ℤ) c ^ 2 / ((1 : LaurentSeries K) - HahnSeries.single (j : ℤ) c) ^ 3 =
      HahnSeries.ofPowerSeries ℤ K (PowerSeries.mk fun n => if j ∣ n then (((n / j).choose 2 : ℕ) : K) * c ^ (n / j) else 0) := by sorry
