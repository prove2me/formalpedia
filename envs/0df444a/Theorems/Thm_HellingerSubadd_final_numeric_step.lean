-- Prove2me | Theorems.Thm_HellingerSubadd_final_numeric_step
-- name    : HellingerSubadd.final_numeric_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:55:30.481161+00:00
-- url     : https://prove2.me/theorems/4d45c648-d758-4b78-af3f-af463c65e7c0
-- title:
--   Numerical step $2(6\log(96n)+\tfrac{18}{96n})\le10^2\log n$ (corrected: $n\ge2$; false at $n=1$)
-- statement:
--   For every natural number $n\ge2$,
--
--   $$
--   2\Bigl(6\log(96n)+\frac{18}{96n}\Bigr)\le10^2\log(n),
--   $$
--
--   with $\log$ the natural logarithm. Together with the rearranged bound it gives the constant $10^2\log n$ of (97).
--
--   Differences from the source:
--   - correction: the inequality for the n of Lemma A.13 (no lower bound) → hypothesis 2 ≤ n; reason: false at n = 1: the left side is 2(6 log 96 + 18/96) ≈ 55.15 and the right side 10² log 1 = 0; it holds for all n ≥ 2 (≈ 63.28 ≤ ≈ 69.31 at n = 2, and the difference of the sides increases with n)
-- source:
--   Foster, Kakade, Qian & Rakhlin, The Statistical Complexity of Interactive Decision Making, arXiv:2112.13487v3, proof of Lemma A.13, p. 74 (last sentence)

import Mathlib

namespace HellingerSubadd

/-- **The numerical step `2(6 log(96n) + 18/(96n)) ≤ 10² log(n)` for `n ≥ 2`.**
Foster, Kakade, Qian & Rakhlin, *The Statistical Complexity of Interactive Decision Making*,
arXiv:2112.13487v3, proof of Lemma A.13, p. 74: "To conclude, we note that
2(6 log(96n) + 18/(96n)) ≤ 10² log(n). This establishes (97)."

**Formalization Note.** *Correction*: the paper states the inequality for the `n` of Lemma A.13
with no lower bound. It is false at `n = 1` (the left side is `2(6 log 96 + 18/96) ≈ 55.15`, the
right side `0`); it holds for every `n ≥ 2` (at `n = 2`: `≈ 63.28 ≤ ≈ 69.31`, and the difference
of the two sides is increasing in `n`). `log` is the natural logarithm; `10 ^ 2 = 100`. -/
theorem final_numeric_step (n : ℕ) (hn : 2 ≤ n) :
    2 * (6 * Real.log (96 * (n : ℝ)) + 18 / (96 * (n : ℝ))) ≤ 10 ^ 2 * Real.log n := by sorry

end HellingerSubadd
