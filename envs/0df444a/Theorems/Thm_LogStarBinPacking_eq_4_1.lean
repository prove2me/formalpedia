-- Prove2me | Theorems.Thm_LogStarBinPacking_eq_4_1
-- name    : LogStarBinPacking.eq_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:29:36.455226+00:00
-- url     : https://prove2.me/theorems/989ccaf2-f892-48ff-9d45-38a8198ae41b
-- title:
--   (4.1) — $\log^*(ax^b)\le\log^*x+O(1)$
-- statement:
--   For fixed reals $a,b>0$,
--   $$
--   \log^*(a x^b)\ \le\ \log^*x+O(1)\qquad(x\to\infty):
--   $$
--   there are constants $C$ and $x_0$ with $\log^*(ax^b)\le\log^*x+C$ for all $x\ge x_0$.
--
--   It converts $\log^*$ of the polynomial size $M$ of the final instance back to $\log^*n$ in the proof of Theorem 1.1.
--
--   Differences from the source:
--   - encoding: log∗ x for x ≥ 1; O(1) as x → ∞ → the published total logStar on ℝ; constants C and x₀; reason: the statement concerns large x only
-- source:
--   I. Doron-Arad, Additive Ω(log∗ OPT) Gap for Bin Packing with Three Items per Bin, manuscript (sha256 1d88425d…), (4.1), p.16

import Mathlib
import Definitions.Def_PacketRouting_CongDil_Recurrences

namespace LogStarBinPacking

/-- **The bound (4.1).** Doron-Arad, *Additive Ω(log∗ OPT) Gap for Bin Packing with Three Items per Bin*, manuscript (sha256 1d88425d…), (4.1), p.16.
For fixed `a, b > 0`, `log∗(a x^b) ≤ log∗ x + O(1)` as `x → ∞`.

**Formalization Note** `log∗` is the published `logStar` (least number of base-two logarithms
bringing the argument to at most one). `O(1)` as `x → ∞` is a constant `C` and a threshold
`x₀`, both depending on `a, b`; `x^b` is the real power. -/
theorem eq_4_1 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      (PacketRouting.CongDil.logStar (a * x ^ b) : ℝ) ≤
        (PacketRouting.CongDil.logStar x : ℝ) + C := by sorry

end LogStarBinPacking
