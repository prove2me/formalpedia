-- Prove2me | Theorems.Thm_ModularCurve_coeff_slotSubst_tateUnivX
-- name    : ModularCurve.coeff_slotSubst_tateUnivX
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/21920c46-f778-505a-8f95-4d7a68b4b257
-- title:
--   Coefficients of the universal Tate x-series after slot substitution
-- statement:
--   Let $K$ be a commutative ring, let $p$ and $j$ be natural numbers with $0 < j$ and $j < p$, let $c$ be a unit of $K$, and let $n$ be a natural number. Here `tateUnivX` is the two-variable power series over $\mathbb Z$ whose coefficient at an exponent vector $e \colon \mathrm{Fin}\,2 \to \mathbb N$ is $-2\sum_{d \mid e_1} d$ when $e_0 = e_1$, is $e_0 - e_1$ when $e_1 < e_0$ and $e_0 - e_1$ divides $e_1$, is $e_1 - e_0$ when $e_0 < e_1$ and $e_1 - e_0$ divides $e_1$, and is $0$ otherwise; and `slotSubst K p c j` is substitution of the pair of one-variable series $\bigl(c\,X^{j},\ c^{-1}X^{\,p-j}\bigr)$ over $K$ into a two-variable series. The assertion is the identity $$\mathrm{coeff}_n\bigl(\mathrm{slotSubst}\,K\,p\,c\,j\,(\mathrm{tateUnivX})\bigr) = \bigl[\,j \mid n\,\bigr]\,(n/j)\,c^{\,n/j} + \sum_{M=0}^{n}\ \sum_{e \mid M} e\Bigl( [\,n = pM + je\,]\,c^{\,e} + [\,n + je = pM\,]\,c^{-e} - 2\,[\,n = pM\,]\Bigr),$$ the bracketed conditions denoting the corresponding indicator values in $K$ and $n/j$ the natural-number quotient; the divisor sum is over the divisors of $M$ in the sense of `Nat.divisors`, so the term $M = 0$ contributes nothing.
--
--   This is the explicit coefficient expansion of the universal Tate $x$-series in the variable $q$ after the substitution sending the toric parameter to $c\,q^{j}$ and the Tate period to $q^{p}$, the three indicator conditions recording the exponents of $q$ in $u^{e}Q^{M}$, $u^{-e}Q^{M}$ and $Q^{M}$. It is the coefficient bookkeeping used throughout the full-level arguments that compare a slot point of parameter $c\,q^{j}$ with the corresponding point of the Tate curve, and is invoked by the statements producing variable changes taking weight-one Tate bases into Laurent base changes together with the attendant cusp data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coeff_slotSubst_tateUnivX.lean

import Definitions.Def_ModularCurve_TateSlots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.coeff_slotSubst_tateUnivX {K : Type*} [CommRing K] (p : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) (n : ℕ) : PowerSeries.coeff n (slotSubst K p c j tateUnivX) = (if j ∣ n then ((n / j : ℕ) : K) * (c : K) ^ (n / j) else 0) + ∑ M ∈ Finset.range (n + 1), ∑ e ∈ M.divisors, (e : K) * ((if n = p * M + j * e then (c : K) ^ e else 0) + (if n + j * e = p * M then ((c⁻¹ : Kˣ) : K) ^ e else 0) - (if n = p * M then 2 else 0)) := by sorry
