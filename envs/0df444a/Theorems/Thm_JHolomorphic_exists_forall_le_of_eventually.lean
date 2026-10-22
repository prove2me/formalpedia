-- Prove2me | Theorems.Thm_JHolomorphic_exists_forall_le_of_eventually
-- name    : JHolomorphic.exists_forall_le_of_eventually
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T23:53:31.281102+00:00
-- url     : https://prove2.me/theorems/9019491e-7464-4fb7-98e3-4a0d05447346
-- title:
--   An eventually bounded sequence of finite extended reals is bounded
-- statement:
--   Let $(a_\nu)_{\nu\in\mathbb N}$ be a sequence in $[0,\infty]$ with $a_\nu<\infty$ for every $\nu$. If there are $N$ and $C\ge0$ with $a_\nu\le C$ for all $\nu\ge N$, then there is $C'\ge0$ with $a_\nu\le C'$ for all $\nu$.
--   This lets uniform bounds be proved only for large indices.
--
--   **Formalization Note** `f : ℕ → ℝ≥0∞` with `f ν ≠ ⊤`; the constants are `ℝ≥0`, coerced to `ℝ≥0∞`.
-- source:
--   Elementary; used for C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Lecture 2, Theorem 2.22

import Definitions.Def_JHolomorphic_Setting
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

namespace JHolomorphic

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal

/-- A sequence in `[0, ∞)` (no value `∞`) that is bounded by a constant for all large indices
is bounded by a constant for all indices. -/
theorem exists_forall_le_of_eventually {f : ℕ → ℝ≥0∞} (hf : ∀ ν, f ν ≠ ⊤)
    (h : ∃ N : ℕ, ∃ C : ℝ≥0, ∀ ν, N ≤ ν → f ν ≤ C) : ∃ C : ℝ≥0, ∀ ν, f ν ≤ C := by
  sorry

end JHolomorphic
