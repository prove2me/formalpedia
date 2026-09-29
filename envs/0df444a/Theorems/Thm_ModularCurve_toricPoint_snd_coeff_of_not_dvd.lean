-- Prove2me | Theorems.Thm_ModularCurve_toricPoint_snd_coeff_of_not_dvd
-- name    : ModularCurve.toricPoint_snd_coeff_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/5c393a75-6eb0-5451-a6f5-da5b0e6b9242
-- title:
--   Toric point's second coordinate is supported on multiples of p
-- statement:
--   Let $K$ be a field, let $p$ be a natural number, let $c \in K$, and let $m$ be a natural number with $p \nmid m$. Recall that `toricPoint K p c` is the pair of Laurent series over $K$ obtained by applying `HahnSeries.ofPowerSeries` to two power series in a variable $q$; its second component is the image of the power series whose $m$-th coefficient is $c^2/(1-c)^3$ for $m = 0$ and, for $m \neq 0$,
--   $$\sum_{d \mid m,\ p \mid d}\Big(\binom{m/d}{2} c^{m/d} - \binom{m/d+1}{2} c^{-(m/d)}\Big) \;+\; \begin{cases} \sum_{e \mid m/p} e & \text{if } p \mid m,\\ 0 & \text{otherwise,}\end{cases}$$
--   the binomial coefficients being read in $K$. The assertion is that the coefficient of this Laurent series at the integer index $m$ is $0$. Since $p \mid 0$, the hypothesis forces $m \neq 0$, so the constant term is untouched; and no divisor of $m$ is divisible by $p$, so the divisor sum is empty as well.
--
--   This is the support half of the coefficient description of the second (ordinate) coordinate of the toric points attached to the Tate parametrisation: together with the constant-term and divisor-sum companions it expresses that this coordinate is $c^2/(1-c)^3$ plus a power series in $q^p$, as befits a function of $c$ and of the parameter $q^p$ alone. It is used in [`ModularCurve.tateUniv_equation`](thm.html#ModularCurve.tateUniv_equation), in [`ModularCurve.toricPoint_equation`](thm.html#ModularCurve.toricPoint_equation), and in the identification of the image of a toric point under the degree-two Vélu-type coordinate maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_toricPoint_snd_coeff_of_not_dvd.lean

import Definitions.Def_ModularCurve_TateSlots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.toricPoint_snd_coeff_of_not_dvd (K : Type*) [Field K] (p : ℕ) (c : K) {m : ℕ} (hpm : ¬ p ∣ m) : (toricPoint K p c).2.coeff (m : ℤ) = 0 := by sorry
