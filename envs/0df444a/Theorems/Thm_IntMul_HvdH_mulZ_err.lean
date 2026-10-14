-- Prove2me | Theorems.Thm_IntMul_HvdH_mulZ_err
-- name    : IntMul.HvdH.mulZ_err
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-12T02:51:54.902994+00:00
-- url     : https://prove2.me/theorems/c9604476-a15b-439a-8d55-69248edc524c
-- title:
--   Error of the fixed-point complex product
-- statement:
--   Let $a,b\in\mathbb Z[i]$ with $|a|\le 2^p$, and let $x,y\in\mathbb C$ with $|y|\le1$. The fixed-point product $\mathrm{mulZ}_p(a,b)=\rho_0(ab/2^p)$ (both parts rounded towards zero) approximates $2^p\,xy$ with
--   $$\bigl|\mathrm{mulZ}_p(a,b)-2^p\,xy\bigr|\le |a-2^p x|+|b-2^p y|+\sqrt2 .$$
--   This is the fixed-point multiplication error estimate (Lemma 2.4 and Corollary 2.10 of Harvey–van der Hoeven) in the form used for twiddle factors, chirps and pointwise products.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Lemma 2.4, Corollary 2.10

import Definitions.Def_IntMul_HvdH_ConvC

namespace IntMul.HvdH
theorem mulZ_err (p : ℕ) (a b : ℤ × ℤ) (x y : ℂ) (ha : ‖gC a‖ ≤ 2 ^ p) (hy : ‖y‖ ≤ 1) :
    ‖gC (mulZ p a b) - 2 ^ p * (x * y)‖ ≤
      ‖gC a - 2 ^ p * x‖ + ‖gC b - 2 ^ p * y‖ + Real.sqrt 2 := by sorry
end IntMul.HvdH
