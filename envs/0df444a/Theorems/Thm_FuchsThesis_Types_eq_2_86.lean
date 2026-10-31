-- Prove2me | Theorems.Thm_FuchsThesis_Types_eq_2_86
-- name    : FuchsThesis.Types.eq_2_86
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:20:59.575524+00:00
-- url     : https://prove2.me/theorems/5dd03acc-2ed5-404d-8759-19a85555c6d8
-- title:
--   Eq. (2.86): $m!/n!\ge n^{m-n}$
-- statement:
--   For natural numbers $m$ and $n$,
--
--   $$
--   \frac{m!}{n!}\ge n^{m-n},
--   $$
--
--   both when $m\ge n$ and when $m<n$, in which case the exponent is negative. This elementary factorial bound is the inequality that compares two multinomial coefficients.
--
--   **Formalization Note** The exponent is an integer, so the power is an integer power. At $n=0$ the right side is $1$ for $m=0$ and $0$ otherwise, and the inequality holds there as well.
--
--   Differences from the source:
--   - encoding: n^(m−n) for unquantified m, n in the factorial → integer power with m, n arbitrary natural numbers, 0^0 = 1; reason: the exponent may be negative, and the source applies the inequality with n replaced by n p0(b), which may be 0.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, eq. (2.86), p.27

import Mathlib

set_option autoImplicit false

namespace FuchsThesis.Types

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, (2.86), p.27 (PDF 36): `m! / n! ≥ n^(m - n)` for natural numbers `m`, `n`,
in both of the source's cases `m ≥ n` and `m < n`.

**Formalization Note.** The exponent `m - n` can be negative, so it is an integer and the power is
`zpow`. At `n = 0` the right side is `0 ^ m`, which is `1` at `m = 0` and `0` otherwise; the
inequality holds there too, and the source's proof applies (2.86) with `n` replaced by `n p0(b)`,
which may vanish. -/
theorem eq_2_86 (m n : ℕ) :
    (n : ℝ) ^ ((m : ℤ) - (n : ℤ)) ≤ (Nat.factorial m : ℝ) / (Nat.factorial n : ℝ) := by sorry

end FuchsThesis.Types
