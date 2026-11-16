-- Prove2me | Theorems.Thm_HWMaskLeak_Supplement_theorem_6
-- name    : HWMaskLeak.Supplement.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:03:04.991095+00:00
-- url     : https://prove2.me/theorems/bc3dc4e8-396c-427d-8a6a-80ede1f04164
-- title:
--   Theorem 6 — two-share obstruction: $E_2(2^n-1)\ge1-|2^n-N|/N-O(n^{-1/2})\ge\frac23-O(n^{-1/2})$
-- statement:
--   Let $E_2(s)$ be the insecurity of a uniform $2$-party additive sharing of $s\in\mathbb Z/N\mathbb Z$ under Hamming-weight leakage, eq. (1), for a modulus $N\ge2$.
--
--   Let $2^n$ be a power of two closest to $N$. For $s=2^n-1\pmod N$,
--   $$
--   E_2(s)\ \ge\ 1-\frac{|2^n-N|}{N}-O\bigl(n^{-1/2}\bigr)\ \ge\ \frac23-O\bigl(n^{-1/2}\bigr),
--   $$
--   where the implied constant is absolute.
--
--   Two shares are never enough under Hamming-weight leakage: for every modulus there is a secret whose shares are, with probability at least about $2/3$, complementary binary strings, and their weights then sum to $n$.
--
--   **Formalization Note** A single constant $C$ realizes both $O(n^{-1/2})$ terms; the power $n^{-1/2}$ is a real power.
--
--   Differences from the source:
--   - encoding: O(n^{−1/2}) (twice) → C · n^{−1/2} with one absolute C > 0 chosen before N and n, used in both inequalities; reason: p.16: O(·) without subscript is absolute; the second inequality is equivalent to |2ⁿ − N|/N ≤ 1/3 whatever the constant
--   - encoding: any modulus N → N : ℕ with [NeZero N] and 2 ≤ N; reason: at N = 1 the closest power is 2⁰, n = 0 and n^{−1/2} is undefined; the paper's moduli are N ≥ 2 (Lemma 3.1, p.18); for N ≥ 2 every closest power has n ≥ 1
--   - encoding: 2ⁿ a power of two closest to N → ∀ j : ℕ, |N − 2ⁿ| ≤ |N − 2ʲ| (ties allowed); reason: 'a power of two closest' admits either of two equidistant powers
--   - encoding: s = 2ⁿ − 1 (mod N) → ((2 ^ n - 1 : ℕ) : ZMod N); reason: 2ⁿ ≥ 1, so the natural subtraction is exact
-- source:
--   Biswas, Hwang, Maji, Shkredov, Ye, When Masks Leak Their Weight: From Additive Sharing to Learning with Physical Rounding, preprint (version of October 31, 2026, sha256 ab686360358eddae84b7b4ee1bbb418105b7887539046e553046bbedd46125a9), Theorem 6, p.28 (pdf p.28), §5.3; proof p.29

import Mathlib
import Definitions.Def_HWMaskLeak_insecurity

namespace HWMaskLeak.Supplement

open HWMaskLeak

/-- **Theorem 6 (the two-share obstruction)** (Biswas, Hwang, Maji, Shkredov, Ye, *When Masks Leak Their Weight: From Additive Sharing to
Learning with Physical Rounding*, preprint (version of October 31, 2026, sha256 ab686360…), Theorem 6, p.28): let `2ⁿ` be a power of two
closest to `N`. For `s = 2ⁿ − 1 (mod N)`,
`E₂(s) ⩾ 1 − |2ⁿ − N|/N − O(n^{−1/2}) ⩾ 2/3 − O(n^{−1/2})`.

**Formalization Note** `E₂(s)` is the published `insecurity N 2 s` (eq. (1)). The `O(·)` is absolute
(convention of p.16): one constant `C`, chosen before `N` and `n`, serves both inequalities. "A power
of two closest to `N`" is `|N − 2ⁿ| ⩽ |N − 2ʲ|` for every `j` (ties allowed). `N ⩾ 2` is the paper's
standing range of moduli (Lemma 3.1, p.18); at `N = 1` the closest power is `2⁰` and `n^{−1/2}` is
undefined. For `N ⩾ 2` every closest power has `n ⩾ 1`. The secret is `2ⁿ − 1` reduced mod `N`. -/
theorem theorem_6 :
    ∃ C : ℝ, 0 < C ∧ ∀ (N n : ℕ) [NeZero N], 2 ≤ N →
      (∀ j : ℕ, |(N : ℝ) - 2 ^ n| ≤ |(N : ℝ) - 2 ^ j|) →
      1 - |(2 : ℝ) ^ n - N| / N - C * (n : ℝ) ^ (-(1 : ℝ) / 2) ≤
          insecurity N 2 (((2 ^ n - 1 : ℕ)) : ZMod N) ∧
        2 / 3 - C * (n : ℝ) ^ (-(1 : ℝ) / 2) ≤
          1 - |(2 : ℝ) ^ n - N| / N - C * (n : ℝ) ^ (-(1 : ℝ) / 2) := by sorry

end HWMaskLeak.Supplement
