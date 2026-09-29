-- Prove2me | Theorems.Thm_ModularCurve_toricPoint_fst_coeff_mul
-- name    : ModularCurve.toricPoint_fst_coeff_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/66af8f1a-b187-5b2a-a7ce-caea8172c84a
-- title:
--   The q^{pM}-coefficient of a toric point's first coordinate
-- statement:
--   Let $K$ be a field, let $p$ be a natural number with $0 < p$, let $c \in K$, and let $M$ be a nonzero natural number. Recall that `toricPoint K p c` is the pair of Laurent series over $K$ obtained by embedding two power series in $\mathbb{Z}$-indexed Hahn series, the first of which has $m$-th coefficient $c/(1-c)^2$ for $m = 0$ and, for $m \neq 0$, $$\sum_{d \mid m,\; p \mid d} \frac{m}{d}\Bigl(c^{m/d} + (c^{-1})^{m/d}\Bigr) \;-\; 2\Bigl(\sum_{e \mid m/p} e\Bigr)\!\cdot\![p \mid m],$$ the last bracket meaning that the subtracted term is present only when $p$ divides $m$, all integer coefficients being read in $K$. The assertion is that the coefficient of this first Laurent series in degree $(pM : \mathbb{Z})$, the image of the natural number $pM$, equals $$\sum_{e \mid M} e\,\bigl(c^{e} + (c^{-1})^{e} - 2\bigr),$$ the sum over the divisors of $M$, again with $e$ read in $K$. No hypothesis is placed on $c$; when $c = 0$ the inverse is $0$ by convention.
--
--   This is the lattice (non-constant-term) part of the coefficient description of the first Tate-parametrisation coordinate attached to a point of constant parameter $c$ on the Tate curve with parameter $q^{p}$: the classical series $u/(1-u)^2 + \sum_{n \geq 1}\bigl(Q^{n}u/(1-Q^{n}u)^2 + Q^{n}u^{-1}/(1-Q^{n}u^{-1})^2 - 2Q^{n}/(1-Q^{n})^2\bigr)$ with $Q = q^{p}$, $u = c$, whose $Q^{M}$-coefficient is the displayed divisor sum. It feeds the verification that the toric points satisfy the Tate curve equation and the compatibility of these points with the $q$-expansion and isogeny maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_toricPoint_fst_coeff_mul.lean

import Definitions.Def_ModularCurve_TateSlots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.toricPoint_fst_coeff_mul (K : Type*) [Field K] (p : ℕ) (hp : 0 < p) (c : K) {M : ℕ} (hM : M ≠ 0) : (toricPoint K p c).1.coeff ((p * M : ℕ) : ℤ) = ∑ e ∈ M.divisors, (e : K) * (c ^ e + c⁻¹ ^ e - 2) := by sorry
