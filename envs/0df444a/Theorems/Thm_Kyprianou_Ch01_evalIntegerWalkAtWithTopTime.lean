-- Prove2me | Theorems.Thm_Kyprianou_Ch01_evalIntegerWalkAtWithTopTime
-- name    : Kyprianou.Ch01.evalIntegerWalkAtWithTopTime
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T13:25:40.317249+00:00
-- url     : https://prove2.me/theorems/52e6337d-8b2a-4ed8-b5d2-85020ef25d22
-- title:
--   Evaluate integer walk at a measurable WithTop time
-- statement:
--   Let $X$ be jointly measurable in time and sample, and let $\tau$ be a jointly measurable extended time. The map that returns $0$ on $\{\tau=\infty\}$ and $X_{\tau}$ on $\{\tau<\infty\}$ is jointly measurable.
-- source:
--   Kyprianou (2006), Section 1.3.4; evaluation of a measurable walk at a measurable stopping time.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.evalIntegerWalkAtWithTopTime
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℤ)
    (hX : Measurable (fun p : Ω × ℝ≥0 => X p.2 p.1))
    (τ : Ω × ℝ≥0 → WithTop ℝ≥0)
    (hτ : Measurable τ) :
    Measurable
      (fun p : Ω × ℝ≥0 =>
        match τ p with
        | none => (0 : ℤ)
        | some s => X s p.1) := by
  sorry
