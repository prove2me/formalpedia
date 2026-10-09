-- Prove2me | Theorems.Thm_IntMul_HvdH_rosser_schoenfeld_thm4
-- name    : IntMul.HvdH.rosser_schoenfeld_thm4
-- status  : Open
-- author  : @avi
-- created : 2026-10-08T23:46:47.612335+00:00
-- url     : https://prove2.me/theorems/afc752db-64d3-4767-8838-0cd754fd9c80
-- title:
--   Rosser–Schoenfeld: $|\vartheta(y)-y|<y/(2\log y)$ for $y\ge 563$
-- statement:
--   Let $\vartheta(y)=\sum_{p\le y}\log p$ be Chebyshev's function, where the sum runs over the primes $p\le y$ and $\log$ is the natural logarithm. For every real $y\ge563$,
--   $$y-\frac{y}{2\log y}<\vartheta(y)<y+\frac{y}{2\log y}.$$
--
--   This is an explicit form of the prime number theorem, $\vartheta(y)\sim y$, with an error term of size $y/(2\log y)$ valid from $y=563$ onward. Harvey and van der Hoeven use it to prove Lemma 5.1, which finds many primes in short intervals $\big((1-2\eta)x,(1-\eta)x\big]$. Those primes are the transform lengths in their $O(n\log n)$ multiplication algorithm.
--
--   **Formalization Note** $\vartheta$ is Mathlib's `Chebyshev.theta`. The statement is the two-sided bound for $y\ge563$ exactly as Harvey and van der Hoeven quote it from Rosser–Schoenfeld (1962), Theorem 4, in the proof of their Lemma 5.1. Rosser and Schoenfeld's original theorem may state the two inequalities with different ranges of validity. Any such version implies this one on $y\ge563$.
-- source:
--   J. B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962) 64-94, Theorem 4, https://doi.org/10.1215/ijm/1255631807; stated in this two-sided form for y >= 563 as quoted in D. Harvey, J. van der Hoeven, Integer multiplication in time O(n log n), Ann. of Math. 193 (2021), proof of Lemma 5.1, p. 37 (preprint https://hal.science/hal-02070778v2)

import Mathlib

namespace IntMul.HvdH

theorem rosser_schoenfeld_thm4 (y : ℝ) (hy : 563 ≤ y) :
    y - y / (2 * Real.log y) < Chebyshev.theta y ∧
      Chebyshev.theta y < y + y / (2 * Real.log y) := by sorry

end IntMul.HvdH
