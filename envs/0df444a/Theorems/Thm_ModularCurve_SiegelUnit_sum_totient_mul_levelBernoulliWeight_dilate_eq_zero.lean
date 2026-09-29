-- Prove2me | Theorems.Thm_ModularCurve_SiegelUnit_sum_totient_mul_levelBernoulliWeight_dilate_eq_zero
-- name    : ModularCurve.SiegelUnit.sum_totient_mul_levelBernoulliWeight_dilate_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/a6f1a23e-064b-5e48-bff7-65f0863a40ba
-- title:
--   Vanishing of a totient-weighted Bernoulli sum over ℤ/N
-- statement:
--   Let $N$ be a positive natural number and let $s \in \mathbb{Z}/N$ be a nonzero residue class. For $r \in \mathbb{Z}/N$ write $\bar r \in \{0,1,\dots,N-1\}$ for the canonical natural-number representative of $r$, and let $g_r = \gcd(\bar r, N)$, so that $g_0 = N$; the weight attached to $r$ is the natural number $(N / g_r)\,\varphi(g_r)$, formed with natural division (exact here, as $g_r \mid N$) and Euler's totient $\varphi$, then cast to $\mathbb{Z}$. Attached to $r$ is further the integer $6\,\overline{sr}^{\,2} - 6N\,\overline{sr} + N^2$, where $\overline{sr}$ is the canonical representative of the product $s\cdot r$ computed in $\mathbb{Z}/N$ and cast to $\mathbb{Z}$. The theorem asserts that the sum of the products of these two quantities over all $r$ in $\mathbb{Z}/N$,
--   $$\sum_{r \in \mathbb{Z}/N} \frac{N}{\gcd(\bar r, N)}\,\varphi\bigl(\gcd(\bar r, N)\bigr)\Bigl(6\,\overline{sr}^{\,2} - 6N\,\overline{sr} + N^2\Bigr),$$
--   is equal to $0$ in $\mathbb{Z}$. The hypothesis $s \neq 0$ is essential: for $s = 0$ every bracket equals $N^2$ and the sum is positive.
--
--   The quadratic $6t^2 - 6Nt + N^2$ is $6N^2$ times the periodic second Bernoulli function evaluated at $t/N$, and $(N/g_r)\varphi(g_r)$ with $g_r = \gcd(\bar r,N)$ is the number of cusps of $\Gamma(N)$, up to sign, whose representing column has lower entry $r$; the identity is thus the degree-zero statement for the divisor of a power of the Siegel function attached to $(0, s/N)$. It is used in the construction of a peaked exponent vector for Siegel units, [`ModularCurve.SiegelUnit.exists_peaked_exponent`](thm.html#ModularCurve.SiegelUnit.exists_peaked_exponent).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_SiegelUnit_sum_totient_mul_levelBernoulliWeight_dilate_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.SiegelUnit.sum_totient_mul_levelBernoulliWeight_dilate_eq_zero (N : ℕ) [NeZero N]
    (s : ZMod N) (hs : s ≠ 0) :
    ∑ r : ZMod N,
        (((N / Nat.gcd r.val N) * Nat.totient (Nat.gcd r.val N) : ℕ) : ℤ) *
          (6 * (((s * r).val : ℕ) : ℤ) ^ 2 - 6 * (N : ℤ) * (((s * r).val : ℕ) : ℤ) + (N : ℤ) ^ 2) = 0 := by sorry
