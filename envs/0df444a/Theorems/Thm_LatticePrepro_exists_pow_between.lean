-- Prove2me | Theorems.Thm_LatticePrepro_exists_pow_between
-- name    : LatticePrepro.exists_pow_between
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:24:55.997583+00:00
-- url     : https://prove2.me/theorems/3ea316ca-a063-4612-a770-931754fd55f8
-- title:
--   A power of $p$ in the interval $[N, pN)$
-- statement:
--   For all natural numbers $p \ge 2$ and $N \ge 2$ there is an exponent $d \ge 1$ such that
--   $$N \le p^d < p \cdot N.$$
--   Since consecutive powers of $p$ differ by a factor $p$, such a $p^d$ is the least power of $p$ that is at least $N$.
--
--   Construction A.4 takes the extension degree $\delta$ to be the least power of the prime $p$ with $\delta \ge S$ ($S$ the number of assignment coordinates), and the sample field size $q$ to be the least power of $p$ with $q \ge 8 p m B \delta$. The lemma provides these powers together with the upper bounds $\delta < pS$ and $q < 8 p^2 m B \delta$, which give the size bound $q < 8 p^3 m S B$ of Theorem A.8.
--
--   **Formalization Note**: The lemma is stated for any natural number $p \ge 2$, not only primes.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), auxiliary lemma used in Construction A.4 (\label{con:moment-representation}) and the proof of Theorem A.8 (\label{thm:moment-representation-construction}); Lean: LatticePrepro/Basic/Nat.lean, LatticePrepro.exists_pow_between

import Mathlib

theorem LatticePrepro.exists_pow_between {p N : ℕ} (hp : 2 ≤ p) (hN : 2 ≤ N) :
    ∃ d, 1 ≤ d ∧ N ≤ p ^ d ∧ p ^ d < p * N := by sorry
