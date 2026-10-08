-- Prove2me | Theorems.Thm_MassartDKW_Tight_proposition_2_ii
-- name    : MassartDKW.Tight.proposition_2_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:40:38.585993+00:00
-- url     : https://prove2.me/theorems/238b1d91-7a28-471e-94fa-ee1690be0c80
-- title:
--   Proposition 2(ii), p. 1281 — Σ_{j=1}^{n−1} j^{j−1}(n − j)^{n−j} n^{−n} (n choose j) ≤ 1
-- statement:
--   For every integer $n\ge2$,
--   $$\sum_{j=1}^{n-1}j^{j-1}(n-j)^{n-j}n^{-n}\binom nj\le1.$$
--
--   It is the derivative at $\lambda=0$ of $P(D_n^->\lambda)$ divided by $\sqrt n$, plus one, and it yields the crude bound (2.14) used for small $n$ in Proposition 2(iii).
--
--   **Formalization Note** Here $j\ge1$, so the natural-number exponent $j-1$ involves no truncation.
-- source:
--   Massart, The tight constant in the Dvoretzky–Kiefer–Wolfowitz inequality, Ann. Probab. 18 (1990), p. 1281, Proposition 2(ii)

import Mathlib

namespace MassartDKW.Tight

theorem proposition_2_ii (n : ℕ) (hn : 2 ≤ n) :
    ∑ j ∈ Finset.Icc 1 (n - 1),
      (j : ℝ) ^ (j - 1) * ((n : ℝ) - j) ^ (n - j) * ((n : ℝ) ^ n)⁻¹ * (n.choose j) ≤ 1 := by sorry

end MassartDKW.Tight
