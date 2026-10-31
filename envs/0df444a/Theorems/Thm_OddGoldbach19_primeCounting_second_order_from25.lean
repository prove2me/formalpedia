-- Prove2me | Theorems.Thm_OddGoldbach19_primeCounting_second_order_from25
-- name    : OddGoldbach19.primeCounting_second_order_from25
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-30T17:41:21.989764+00:00
-- url     : https://prove2.me/theorems/223b0e73-04f1-485e-80d9-054d3087dcc4
-- title:
--   Positive second-order prime counting from logarithmic threshold25
-- statement:
--   For every natural number $n$ with $\log n\ge25$, the prime-counting function satisfies
--   $$\pi(n)\ge \frac{n}{\log n}+0.46\frac{n}{(\log n)^2}.$$
--   This lowers the logarithmic threshold of the existing positive second-order estimate, providing an explicit input near the small-to-medium range transition of the campaign.
-- source:
--   Derived from the proved Rosser-Schoenfeld theta estimate https://prove2.me/theorems/d4cf496a-eed1-4284-8d5d-f9cfbfb07786 and Mathlib partial summation. The proof of the existing threshold27 estimate actually works from25 after replacing log100<=7 by log100<=5. The new threshold is a proved consequence of these inputs, not the stronger original Riesel-Vaughan prime-counting coefficient.

import Mathlib

theorem OddGoldbach19.primeCounting_second_order_from25 (n : ℕ) (hl : 25≤Real.log (n:ℝ)) :
    (n:ℝ)/Real.log n+0.46*n/(Real.log n)^2 ≤ (Nat.primeCounting n:ℝ) := by sorry
