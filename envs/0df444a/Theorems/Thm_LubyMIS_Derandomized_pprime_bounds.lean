-- Prove2me | Theorems.Thm_LubyMIS_Derandomized_pprime_bounds
-- name    : LubyMIS.Derandomized.pprime_bounds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T22:58:26.122986+00:00
-- url     : https://prove2.me/theorems/5bc47798-159f-4ae7-a868-6f519b41318d
-- title:
--   The modified probabilities satisfy (8/9)·p_i ≤ p′_i ≤ p_i in Case 2
-- statement:
--   Let $q$ be a prime with $n \le q \le 2n$ and let $d$ be a degree with $1 \le d < n/16$. Put $p = 1/(2d)$ and $p' = \lfloor p \cdot q \rfloor / q$. Then
--   $$\tfrac{8}{9}\, p \ \le\ p' \ \le\ p .$$
--
--   Rounding the probability $1/2d(i)$ down to a multiple of $1/q$ therefore loses at most a factor $8/9$ in Case 2 of Algorithm C, which is what Lemma D needs.
--
--   **Formalization Note** $\lfloor p q\rfloor = \lfloor q/2d \rfloor$ is computed by natural-number division `q / (2 * d)`.
-- source:
--   Luby, A Simple Parallel Algorithm for the Maximal Independent Set Problem, SIAM J. Comput. 15(4), 1986, p. 1046, §4.4, paragraph before LEMMA D

import Mathlib

namespace LubyMIS.Derandomized

/-- The bounds on the modified probabilities (Luby 1986, §4.4, p. 1046): for a prime `n ≤ q ≤ 2n`
and a degree `1 ≤ d < n/16`, `p = 1/(2d)` and `p′ = ⌊p·q⌋/q` satisfy `(8/9) p ≤ p′ ≤ p`. -/
theorem pprime_bounds (n q d : ℕ) (hq : q.Prime) (hnq : n ≤ q) (hq2 : q ≤ 2 * n) (hd : 1 ≤ d)
    (h16 : 16 * d < n) :
    8 / 9 * (1 / (2 * (d : ℝ))) ≤ ((q / (2 * d) : ℕ) : ℝ) / q ∧
      ((q / (2 * d) : ℕ) : ℝ) / q ≤ 1 / (2 * (d : ℝ)) := by sorry

end LubyMIS.Derandomized
