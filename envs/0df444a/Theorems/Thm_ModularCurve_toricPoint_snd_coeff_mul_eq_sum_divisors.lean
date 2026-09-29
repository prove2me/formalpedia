-- Prove2me | Theorems.Thm_ModularCurve_toricPoint_snd_coeff_mul_eq_sum_divisors
-- name    : ModularCurve.toricPoint_snd_coeff_mul_eq_sum_divisors
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/6e0d05a0-6cda-5de0-9005-dde325a8f2ad
-- title:
--   The q^{pM}-coefficient of a toric point's second coordinate
-- statement:
--   Let $K$ be a field, let $p$ be a natural number with $0 < p$, let $c \in K$, and let $M$ be a nonzero natural number. The pair `toricPoint K p c` of Laurent series over $K$ has as its second component the image under `HahnSeries.ofPowerSeries` of the power series whose $m$-th coefficient is $c^2/(1-c)^3$ for $m = 0$ and, for $m \neq 0$,
--   $$\Big(\sum_{d \mid m,\; p \mid d} \big(\tbinom{m/d}{2} c^{m/d} - \tbinom{m/d+1}{2} (c^{-1})^{m/d}\big)\Big) + \Big(\sum_{e \mid m/p} e\Big)\,[p \mid m],$$
--   the inner sum over divisors $d$ of $m$ contributing $0$ for those $d$ not divisible by $p$, and the last term being present only when $p \mid m$. The assertion is that the coefficient of this Laurent series in degree $(pM : \mathbb{Z})$ equals
--   $$\sum_{e \mid M} \Big(\tbinom{e}{2}\,(c^{e} - (c^{-1})^{e}) - e\,(c^{-1})^{e} + e\Big),$$
--   the sum being over the divisors $e$ of $M$, with binomial coefficients and divisor indices cast from $\mathbb{N}$ to $K$. All inverses are formed in the field $K$, so $c^{-1} = 0$ when $c = 0$.
--
--   This is the lattice-sum part of the classical description of the $y$-coordinate of the point of Tate parameter $c$ on the Tate curve with parameter $q^{p}$: away from the constant term $c^2/(1-c)^3$, the $q^{pM}$-coefficient is $\sum_{e \mid M}\big(\binom{e}{2}c^{e} - \binom{e+1}{2}c^{-e} + e\big)$, rewritten using $\binom{e+1}{2} = \binom{e}{2} + e$. It is used in the verification that the toric points satisfy the Tate curve equation ([`ModularCurve.tateUniv_equation`](thm.html#ModularCurve.tateUniv_equation), [`ModularCurve.toricPoint_equation`](thm.html#ModularCurve.toricPoint_equation)) and in the compatibility of these points with the isogeny and $q$-expansion maps ([`ModularCurve.vcXInv_velu2X_and_vcYInv_velu2Y_toricPoint_tateLaurent_map_qExpand_eq_toricPoint_sq`](thm.html#ModularCurve.vcXInv_velu2X_and_vcYInv_velu2Y_toricPoint_tateLaurent_map_qExpand_eq_toricPoint_sq)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_toricPoint_snd_coeff_mul_eq_sum_divisors.lean

import Definitions.Def_ModularCurve_TateSlots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.toricPoint_snd_coeff_mul_eq_sum_divisors (K : Type*) [Field K] (p : ℕ) (hp : 0 < p) (c : K) {M : ℕ} (hM : M ≠ 0) : (toricPoint K p c).2.coeff ((p * M : ℕ) : ℤ) = ∑ e ∈ M.divisors, (((e.choose 2 : ℕ) : K) * (c ^ e - c⁻¹ ^ e) - (e : K) * c⁻¹ ^ e + (e : K)) := by sorry
