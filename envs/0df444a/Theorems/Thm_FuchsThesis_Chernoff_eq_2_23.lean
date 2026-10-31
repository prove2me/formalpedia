-- Prove2me | Theorems.Thm_FuchsThesis_Chernoff_eq_2_23
-- name    : FuchsThesis.Chernoff.eq_2_23
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:55:16.069992+00:00
-- url     : https://prove2.me/theorems/afbab4f3-8405-4895-b9ff-0bcaf00bc35d
-- title:
--   Eq. (2.23) — $\min\{a,b\} \le a^\alpha b^{1-\alpha}$ for $0 \le \alpha \le 1$
-- statement:
--   For any two nonnegative real numbers $a, b$ and any $0 \le \alpha \le 1$,
--
--   $$
--   \min\{a, b\} \le a^{\alpha} b^{1-\alpha}.
--   $$
--
--   Applied termwise to $\min\{\pi_0 p_0, \pi_1 p_1\}$ this inequality converts the Bayes error into a sum of products, which factorizes over independent samplings and gives the Chernoff bound.
--
--   **Formalization Note** Real powers use Lean's convention $0^0 = 1$.
--
--   Differences from the source:
--   - generalization: a, b positive → a, b ≥ 0 (real powers with 0^0 = 1); reason: the inequality remains true when a or b is 0, and the statement specializes to the source's for positive a, b
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, §2.2.2, eq. (2.23), p.17 (PDF p.26)

import Mathlib

namespace FuchsThesis.Chernoff

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, §2.2.2, eq. (2.23), p.17 (PDF p.26): for any two positive numbers
`a`, `b` and any `0 ≤ α ≤ 1`, `min{a, b} ≤ a^α b^{1−α}`.

**Formalization Note.** Stated for `a, b ≥ 0` (the source: positive), with `Real.rpow`
(`0 ^ 0 = 1`); it specializes to the source's statement for positive `a`, `b`. -/
theorem eq_2_23 (a b α : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    min a b ≤ a ^ α * b ^ (1 - α) := by sorry

end FuchsThesis.Chernoff
