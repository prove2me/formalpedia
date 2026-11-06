-- Prove2me | Theorems.Thm_ImpatientQPTAS_distinct_values
-- name    : ImpatientQPTAS.distinct_values
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:01:59.31105+00:00
-- url     : https://prove2.me/theorems/458d0b30-8b92-40c9-a8e3-d1884ffa62d2
-- title:
--   §2.3, Property 1, p.10, and §2.2, p.9 — few distinct rounded values
-- statement:
--   There is a universal constant $c>0$ such that for every $\epsilon\in(0,\tfrac14)$, every $n\ge1$ and every instance, the rounded rewards take at most $c\cdot\frac1\epsilon\log\frac n\epsilon$ distinct values, and the rounded probabilities $p^\uparrow_i$, as well as $p^\downarrow_i$, $i\in C_{\mathrm{average}}$, take at most $c\cdot\frac1{\epsilon^2}\log\frac n\epsilon$ distinct values.
--
--   These two counts bound the number of reward-probability classes, and so the size of the dynamic program.
--
--   Differences from the source:
--   - reading: r̃_i is r_i rounded down to the nearest power of 1 + ε → r̃_i is on the grid r_max·(1+ε)^(−j); reason: as in rRound_band; the count is the same
--   - encoding: O(·) → a universal constant c, before ε, n and the instance; n ≥ 1; reason: the meaning of O; with no customers there is nothing to count
--   - encoding: all customers average (§2.3) → images taken over C_average; reason: the reduction of §2.1 assumes C_average = [n]
-- source:
--   Segev, Near-Optimal Adaptive Policies for Serving Stochastically Departing Customers, arXiv:2209.13878v1, §2.2, p.9 ("creates O((1/ε) log(n/ε)) distinct values"); §2.3, Property 1, p.10

import Mathlib
import Definitions.Def_ImpatientQPTAS_Model
import Definitions.Def_ImpatientQPTAS_Classes
import Definitions.Def_ImpatientQPTAS_Rounding

namespace ImpatientQPTAS

/-- Segev, arXiv:2209.13878v1, §2.2, p.9, and §2.3, Property 1, p.10: the rounded rewards take
`O((1/ε)·log(n/ε))` distinct values, and the rounded probabilities `O((1/ε²)·log(n/ε))`.

**Formalization Note.** The constant `c` is universal: it comes before `ε`, `n` and the instance.
Property 1 assumes every customer average, so the images are taken over `C_average`. `log(n/ε) > 0`, as
`n ≥ 1` and `ε < 1/4`. -/
theorem distinct_values :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 4 → ∀ (n : ℕ), 1 ≤ n → ∀ I : Instance n, I.Standing →
      ((Finset.univ.image (rTilde ε I)).card : ℝ) ≤ c * (1 / ε) * Real.log ((n : ℝ) / ε) ∧
      (((Caverage ε I).image (pTilde ε I)).card : ℝ) ≤
        c * (1 / ε ^ 2) * Real.log ((n : ℝ) / ε) ∧
      (((Caverage ε I).image fun i => pDown ε (I.p i)).card : ℝ) ≤
        c * (1 / ε ^ 2) * Real.log ((n : ℝ) / ε) := by sorry

end ImpatientQPTAS
