-- Prove2me | Theorems.Thm_IntMul_HvdH_rosser_schoenfeld_theta_upper
-- name    : IntMul.HvdH.rosser_schoenfeld_theta_upper
-- status  : Open
-- author  : @avi
-- created : 2026-10-09T00:25:15.293326+00:00
-- url     : https://prove2.me/theorems/b81175aa-9f84-40ca-b50d-edfe63a15a37
-- title:
--   Rosser–Schoenfeld upper bound $\vartheta(y) < y + y/(2\log y)$ for $y \ge 563$
-- statement:
--   Let $\vartheta(y) = \sum_{p \le y} \log p$ be Chebyshev's function (sum over primes $p \le y$, natural logarithm). For every real $y \ge 563$,
--   $$\vartheta(y) \;<\; y + \frac{y}{2\log y}.$$
--
--   This is the upper half of Rosser–Schoenfeld's Theorem 4 (which states it on a wider range of $y$), restricted to the range $y \ge 563$ in which Harvey–van der Hoeven quote it in the proof of their Lemma 5.1. Together with the matching lower bound $y - y/(2\log y) < \vartheta(y)$ it gives `IntMul.HvdH.rosser_schoenfeld_thm4`.
--
--   Formalization note: `Chebyshev.theta` is Mathlib's $\vartheta$ on $\mathbb{R}$; since $y \ge 563$, $\log y > 0$ and no junk values arise. The inequality is strict.
-- source:
--   J. B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64–94, Theorem 4, p. 70 (upper bound for θ), https://doi.org/10.1215/ijm/1255631807; as quoted in D. Harvey, J. van der Hoeven, Integer multiplication in time O(n log n), Ann. of Math. 193 (2021), proof of Lemma 5.1, p. 38–39 ([39, Thm. 4]).

import Mathlib

namespace IntMul.HvdH

theorem rosser_schoenfeld_theta_upper (y : ℝ) (hy : 563 ≤ y) :
    Chebyshev.theta y < y + y / (2 * Real.log y) := by sorry

end IntMul.HvdH
