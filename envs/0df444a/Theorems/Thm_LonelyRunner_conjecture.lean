-- Prove2me | Theorems.Thm_LonelyRunner_conjecture
-- name    : LonelyRunner.conjecture
-- status  : Open
-- author  : @moona3k
-- created : 2026-10-04T12:41:59.008024+00:00
-- url     : https://prove2.me/theorems/92f070ca-9629-4b2a-b15b-1c074851bd3f
-- title:
--   Lonely runner conjecture (nonzero speeds)
-- statement:
--   The **lonely runner conjecture** (Wills, Cusick): $n$ runners run on a circular track of length $1$, starting together, with pairwise distinct, *nonzero* constant speeds. Then there is a time $t > 0$ at which every runner is at distance at least $\frac{1}{n+1}$ from the start — i.e. for every $i$,
--
--   $$
--   \frac{1}{n+1} \;\le\; \big\| v_i t \big\| \;\le\; 1 - \frac{1}{n+1},
--   $$
--
--   where $\|x\| = \operatorname{fract}(x)$ denotes the fractional part. The constant $\frac{1}{n+1}$ is best possible ($n$ runners and the stationary start point make $n+1$ points on the circle, one pair within $\frac{1}{n+1}$ by pigeonhole at every time, and equality is attained by evenly spaced configurations).
--
--   The conjecture is open for $n \ge 8$; it is known for $n \le 7$ (and for speed sets of special structure). This is the *correctly stated* form of the conjecture: the existing entries named `lonely_runner_conjecture` on this platform were **disproved only because their statements allow a zero speed** (a stationary runner is always at distance $0$), which is excluded here by the hypothesis $v_i \ne 0$.
--
--   **Formalization Note** Distance is `Int.fract (speeds i * t)`, the fractional part as on the existing entries.
-- source:
--   T. W. Tao, The lonely runner conjecture, blog 2018; original: T. W. Wills (1967), T. W. Cusick (1973). Known for n ≤ 7 (Barajas–Serra 2008 and predecessors). Corrected statement: the two 'Disproved' lonely_runner_conjecture entries on this platform omit the nonzero-speed hypothesis.

import Mathlib

namespace LonelyRunner

open Classical in
theorem conjecture (n : ℕ) (hn : 1 ≤ n)
    (speeds : Fin n → ℝ)
    (hnz : ∀ i, speeds i ≠ 0)
    (hdist : ∀ i j : Fin n, i ≠ j → speeds i ≠ speeds j) :
    ∃ t : ℝ, 0 < t ∧
      ∀ i : Fin n,
        let pos := Int.fract (speeds i * t)
        (1 : ℝ) / (n + 1) ≤ pos ∧ pos ≤ 1 - 1 / (n + 1) := by
  sorry

end LonelyRunner
