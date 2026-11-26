-- Prove2me | Theorems.Thm_LefebvreVariations_kaneko_le_100000
-- name    : LefebvreVariations.kaneko_le_100000
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:18:54.832495+00:00
-- url     : https://prove2.me/theorems/adbd9339-1c8b-4172-9bea-57ba1aaef50e
-- title:
--   Lefebvre's variations, No. 150 — on a theme by Kaneko: the Kaneko harmonic divisor inequality holds for 60 < n <= 100000
-- statement:
--   For every integer $n$ with $60<n\le 100000$,
--   $$
--   \sigma(n)\ \le\ e^{H_n}\,\log H_n ,
--   $$
--   where $\sigma(n)$ is the sum of the divisors of $n$ and $H_n=1+\tfrac12+\dots+\tfrac1n$.
--
--   The parent asserts this for every $n>60$ (listed on the platform among the equivalents of the Riemann hypothesis, in the style of Robin's and Lagarias' criteria). The threshold $60$ is sharp: at $n=60$ one has $\sigma(60)=168>166.30\ldots$.
--
--   **Formalization Note** The conclusion is that of `BroughanRH.kaneko` verbatim (with `harmonic n : ℚ` cast to $\mathbb{R}$ and `Real.log`), with the extra hypothesis `n ≤ 100000`.
--
--   **Why this is a variation.** Variation on the open platform theorem BroughanRH.kaneko (an equivalent of the Riemann hypothesis): the parent's own inequality on the explicit finite range 60 < n <= 100000, where it is a finite computation.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Statement and name as on the platform (BroughanRH.kaneko, from K. Broughan, Equivalents of the Riemann Hypothesis, Cambridge Univ. Press, 2017; the attribution to Kaneko and the exact book reference are cited from memory and could not be confirmed by web search). Related and verified: J. C. Lagarias, An elementary problem equivalent to the Riemann hypothesis, Amer. Math. Monthly 109 (2002), sigma(n) <= H_n + exp(H_n) log H_n. Truth check: the author computed sigma(n) exactly and compared with exp(H_n) log H_n in double precision for all 60 < n <= 200000: no violation, smallest relative margin 0.19%; n = 60 fails (168 > 166.30), n = 61..65 pass.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

theorem kaneko_le_100000 :
    ∀ n : ℕ, 60 < n → n ≤ 100000 →
      ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≤
        Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) := by
  sorry

end LefebvreVariations
