-- Prove2me | Theorems.Thm_HammingSumset729_Approximation_fact_A_2
-- name    : HammingSumset729.Approximation.fact_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:41:50.916773+00:00
-- url     : https://prove2.me/theorems/38d89a38-eacd-4c4f-b8ef-558ff31868a8
-- title:
--   Fact A.2 — occurrence separation
-- statement:
--   Let $P$ be a pattern, $T$ a text, and $x\ge0$ a mismatch threshold. Suppose $\ell$ is the least positive $2x$-period of $P$: shifting $P$ by $\ell$ creates at most $2x$ mismatches in the overlap, and no smaller positive shift has this property. If two distinct valid occurrences start at $i<j$ and each has distance at most $x$ from $P$, then
--
--   $$j-i\ge\ell.$$
--
--   This is the occurrence-separation fact for the nonperiodic kernel branch.
--
--   Differences from the source:
--   - encoding: nonnegative mismatch threshold and distinct occurrence positions → nonnegative real threshold, positive minimal period, and ordered positions i<j; reason: the ordering represents an unordered distinct pair; distance bounds use equal-length valid windows
-- source:
--   Nick Fischer, Yael Kirkpatrick, Vassilios Nakos, STOC 2027 submission #729 (October 2026), Fact A.2, printed p. 23 (PDF p. 25). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/729.pdf

import Definitions.Def_HammingSumset729_Approximation_Strings

set_option autoImplicit false
open scoped ENNReal NNReal

namespace HammingSumset729.Approximation

theorem fact_A_2 {α : Type*} [DecidableEq α] (t p : List α)
    (x : ℝ) (hx : 0 ≤ x) (ell : ℕ) (hperiod : IsMinimalPeriod p (2 * x) ell)
    (i j : ℕ) (hij : i < j) (hi : i + p.length ≤ t.length)
    (hj : j + p.length ≤ t.length)
    (hdi : (shiftDistance t p i : ℝ) ≤ x)
    (hdj : (shiftDistance t p j : ℝ) ≤ x) : ell ≤ j - i := by sorry

end HammingSumset729.Approximation
