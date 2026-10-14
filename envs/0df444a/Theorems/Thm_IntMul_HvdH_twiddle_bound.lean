-- Prove2me | Theorems.Thm_IntMul_HvdH_twiddle_bound
-- name    : IntMul.HvdH.twiddle_bound
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-11T22:10:04.654999+00:00
-- url     : https://prove2.me/theorems/476d2766-2df8-47bd-b620-9c53b6749430
-- title:
--   $n$-bit approximation of roots of unity $e^{2\pi ij/k}$
-- statement:
--   Let $n\ge0$, $k\ge1$ and $j\ge0$ be integers, and let $u+iv$ be the Gaussian integer computed by `twiddle n k j` (see `IntMul_HvdH_Twiddle`). Then
--   $$\bigl|2^{-n}(u+iv)-e^{2\pi ij/k}\bigr|\le 2^{-n}.$$
--   This is the content of Lemma 2.12 of Harvey–van der Hoeven (computing the twiddle factors of the FFT to precision $n$), for an explicit algorithm: reduction of the angle to $[0,\pi/4]$ by exact symmetries of $\mathbb Z[i]$, followed by a fixed-point Taylor series.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Lemma 2.12 (complex exponentials e^{2 pi i j/k})

import Definitions.Def_IntMul_HvdH_Twiddle
import Theorems.Thm_IntMul_HvdH_piBits_bound
import Theorems.Thm_IntMul_HvdH_expBits_bound

namespace IntMul.HvdH
theorem twiddle_bound (n k j : ℕ) (hk : 0 < k) :
    ‖((twiddle n k j).1 : ℂ) + ((twiddle n k j).2 : ℂ) * Complex.I -
      2 ^ n * Complex.exp (2 * Real.pi * Complex.I * j / k)‖ ≤ 1 := by sorry
end IntMul.HvdH
