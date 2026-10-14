-- Prove2me | Theorems.Thm_IntMul_HvdH_expBits_bound
-- name    : IntMul.HvdH.expBits_bound
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-11T22:01:15.229985+00:00
-- url     : https://prove2.me/theorems/a9a28f03-4bcb-43fb-9669-335099aa440f
-- title:
--   $n$-bit approximation of $e^z$ on the unit disc
-- statement:
--   Let $n\ge0$ and let $x,y\in\mathbb Z$ with $|x+iy|\le 2^n$, so that $z=2^{-n}(x+iy)$ lies in the closed unit disc. Let $u+iv$ be the Gaussian integer computed by `expBits n x y` (fixed-point Taylor series with floor rounding at precision $2n+9$, then rounding to precision $n$; see `IntMul_HvdH_ExpApprox`). Then
--   $$\bigl|2^{-n}(u+iv)-e^{z}\bigr|\le 2^{-n}.$$
--   This is the fact used in §2.8 of Harvey–van der Hoeven that $e^z$ can be computed to $n$ bits for $z$ in a fixed bounded set (here the unit disc).
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Section 2.8 (n-bit approximation of exp(z) for bounded z)

import Definitions.Def_IntMul_HvdH_ExpApprox

namespace IntMul.HvdH
theorem expBits_bound (n : ℕ) (x y : ℤ) (h : ‖(x : ℂ) + (y : ℂ) * Complex.I‖ ≤ 2 ^ n) :
    ‖((expBits n x y).1 : ℂ) + ((expBits n x y).2 : ℂ) * Complex.I -
      2 ^ n * Complex.exp (((x : ℂ) + (y : ℂ) * Complex.I) / 2 ^ n)‖ ≤ 1 := by sorry
end IntMul.HvdH
