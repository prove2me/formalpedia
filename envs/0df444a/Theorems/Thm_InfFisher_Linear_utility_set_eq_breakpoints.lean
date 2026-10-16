-- Prove2me | Theorems.Thm_InfFisher_Linear_utility_set_eq_breakpoints
-- name    : InfFisher.Linear.utility_set_eq_breakpoints
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:05:48.015895+00:00
-- url     : https://prove2.me/theorems/014ad671-447e-41b3-a5b8-8d6f7d94cf04
-- title:
--   Proof of Theorem 4, (A.5)–(A.6) — breakpoint utility representation
-- statement:
--   For normalized linear valuations on $[0,1]$ with intercepts $2\ge d_1\ge\cdots\ge d_n\ge0$, membership in the feasible utility set is equivalent to nonnegative utilities and the existence of intermediate breakpoints in $[0,1]$ whose interval utility formulas dominate each coordinate:
--
--   $$u_i\le\frac{c_i}{2}(a_i^2-a_{i-1}^2)+d_i(a_i-a_{i-1}),\quad a_0=0,\ a_n=1.$$
--
--   This is the first breakpoint reformulation in the proof of Theorem 4, immediately before the introduction of the auxiliary $z_i,w_i$ variables in (A.6). The displayed inequalities themselves force the breakpoints into order under the stated valuation assumptions.
--
--   **Formalization Note** Lean buyer $i$ uses endpoints $a_i,a_{i+1}$; $n\ge1$ excludes the inconsistent zero buyer endpoint case.
-- source:
--   Gao & Kroer, Infinite-Dimensional Fisher Markets and Tractable Fair Division, arXiv:2010.03025v5, proof of Theorem 4, (A.5)–(A.6), pp. a10–a11 (PDF 45–46)

import Mathlib
import Definitions.Def_InfFisher_Linear_Setting

namespace InfFisher.Linear

open MeasureTheory

/-- Gao–Kroer, proof of Theorem 4, (A.5)–(A.6): a breakpoint description of `U`. -/
theorem utility_set_eq_breakpoints {n : ℕ} (hn : 0 < n) (c d : ℕ → ℝ)
    (hnorm : ∀ i < n, c i / 2 + d i = 1)
    (hd : ∀ i j, i ≤ j → j < n → d j ≤ d i)
    (hd2 : d 0 ≤ 2) (hd0 : 0 ≤ d (n - 1)) :
    ∀ u : Fin n → ℝ,
      u ∈ feasUtil (volume.restrict (Set.Icc (0 : ℝ) 1)) (linVal c d n) ↔
        (∀ i, 0 ≤ u i) ∧
        ∃ a : ℕ → ℝ,
          a 0 = 0 ∧ a n = 1 ∧
          (∀ k, 1 ≤ k → k ≤ n - 1 → 0 ≤ a k ∧ a k ≤ 1) ∧
          ∀ i : Fin n,
            u i ≤ c i.val / 2 * (a (i.val + 1) ^ 2 - a i.val ^ 2) +
              d i.val * (a (i.val + 1) - a i.val) := by sorry

end InfFisher.Linear
