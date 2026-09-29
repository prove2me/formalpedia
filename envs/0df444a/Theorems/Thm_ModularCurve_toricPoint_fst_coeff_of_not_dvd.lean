-- Prove2me | Theorems.Thm_ModularCurve_toricPoint_fst_coeff_of_not_dvd
-- name    : ModularCurve.toricPoint_fst_coeff_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/10104026-eae4-5e8c-a346-80cd086825c4
-- title:
--   Vanishing of q^m-coefficients of the toric x-coordinate for p ∤ m
-- statement:
--   Let $K$ be a field, let $p$ and $m$ be natural numbers with $p \nmid m$, and let $c \in K$. The point `toricPoint K p c` is the pair of Laurent series over $K$ (Hahn series on $\mathbb{Z}$) obtained by pushing forward two explicit power series in $q$; its first component has $q$-coefficients $c/(1-c)^2$ in degree $0$ and, in degree $m \ge 1$,
--   $$\sum_{d \mid m,\; p \mid d} \frac{m}{d}\left(c^{m/d} + (c^{-1})^{m/d}\right) \;-\; 2\left(\sum_{e \mid m/p} e\right)\!\cdot\![\,p \mid m\,],$$ where the second term is present only when $p \mid m$. The assertion is that under $p \nmid m$ the coefficient of this first component at the integer index $m$ is $0$. (Since $p \mid 0$, the hypothesis forces $m \ne 0$, so the constant term is untouched; $p$ is an arbitrary natural number, not assumed prime, and for $p = 1$ the hypothesis is never satisfied.) Equivalently: no divisor of $m$ is divisible by $p$, so the divisor sum is identically zero and the correction term is absent.
--
--   This is the support half of the coefficient description of the $x$-coordinate of the toric point: the series is concentrated on exponents divisible by $p$, as befits a coordinate that classically depends only on the parameters $c$ and $q^p$. It is used in the verification of the defining equations [`ModularCurve.tateUniv_equation`](thm.html#ModularCurve.tateUniv_equation) and [`ModularCurve.toricPoint_equation`](thm.html#ModularCurve.toricPoint_equation), and in the compatibility of the toric point with the $q$-expansion and Vélu-type coordinate maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_toricPoint_fst_coeff_of_not_dvd.lean

import Definitions.Def_ModularCurve_TateSlots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.toricPoint_fst_coeff_of_not_dvd (K : Type*) [Field K] (p : ℕ) (c : K) {m : ℕ} (hpm : ¬ p ∣ m) : (toricPoint K p c).1.coeff (m : ℤ) = 0 := by sorry
