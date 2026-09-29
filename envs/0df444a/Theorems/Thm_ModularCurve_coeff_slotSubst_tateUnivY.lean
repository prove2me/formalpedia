-- Prove2me | Theorems.Thm_ModularCurve_coeff_slotSubst_tateUnivY
-- name    : ModularCurve.coeff_slotSubst_tateUnivY
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/b7fba96b-9051-58d1-9601-13e56143dab6
-- title:
--   Coefficients of a slot substitution into the universal Tate Y-series
-- statement:
--   Let $K$ be a commutative ring, let $p$ and $j$ be natural numbers with $0 < j$ and $j < p$, and let $c$ be a unit of $K$. Recall that `tateUnivY` is the power series in two variables over $\mathbb{Z}$ whose coefficient at the exponent vector $(a,b)$ is $\sum_{d \mid b} d$ when $a = b$, is $\binom{a-b}{2}$ when $b < a$ and $a-b$ divides $b$, is $-\binom{(b-a)+1}{2}$ when $a \le b$, $a \neq b$ and $b-a$ divides $b$, and is $0$ in the remaining two (divisibility-failing) cases; and that `slotSubst K p c j` substitutes $X_0 \mapsto c\,X^{j}$ and $X_1 \mapsto c^{-1}X^{\,p-j}$, producing a one-variable power series over $K$. The assertion is that for every natural number $n$ the coefficient of $X^{n}$ in `slotSubst K p c j tateUnivY` equals the head term $\binom{n/j}{2}\,c^{\,n/j}$ if $j \mid n$ and $0$ otherwise, plus the finite double sum over $M$ with $0 \le M \le n$ and over the divisors $e$ of $M$ of the expression $\binom{e}{2}c^{e}$ if $n = pM + je$ (else $0$), minus $\binom{e+1}{2}(c^{-1})^{e}$ if $n + je = pM$ (else $0$), plus $e$ if $n = pM$ (else $0$), all binomial coefficients being natural numbers mapped into $K$.
--
--   This is the explicit $q$-expansion, after a substitution $u = c\,q^{j}$, $Q = q^{p}$, of the universal $Y$-coordinate series of the Tate curve, reorganised as a head term together with a double divisor sum; the three indicator conditions record the contributions of the positive, negative and diagonal parts of the two-variable series. It is the computational basis for the cusp-data constructions that use it, such as [`ModularCurve.coeff_zero_two_mul_cuspPoint_snd_add_fst`](thm.html#ModularCurve.coeff_zero_two_mul_cuspPoint_snd_add_fst), [`ModularCurve.cuspData_map_coeffMap`](thm.html#ModularCurve.cuspData_map_coeffMap) and [`ModularCurve.cuspData_map_qTwist`](thm.html#ModularCurve.cuspData_map_qTwist).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coeff_slotSubst_tateUnivY.lean

import Definitions.Def_ModularCurve_TateSlots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.coeff_slotSubst_tateUnivY {K : Type*} [CommRing K] (p : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) (n : ℕ) : PowerSeries.coeff n (slotSubst K p c j tateUnivY) = (if j ∣ n then (((n / j).choose 2 : ℕ) : K) * (c : K) ^ (n / j) else 0) + ∑ M ∈ Finset.range (n + 1), ∑ e ∈ M.divisors, ((if n = p * M + j * e then ((e.choose 2 : ℕ) : K) * (c : K) ^ e else 0) - (if n + j * e = p * M then (((e + 1).choose 2 : ℕ) : K) * ((c⁻¹ : Kˣ) : K) ^ e else 0) + (if n = p * M then (e : K) else 0)) := by sorry
